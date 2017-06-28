
open Prims
open FStar_Pervasives
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____5 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail = (fun r msg -> ((

let uu____98 = (

let uu____99 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____99 msg))
in (FStar_All.pipe_left FStar_Util.print_string uu____98));
(failwith msg);
))


let err_uninst = (fun env t uu____133 app -> (match (uu____133) with
| (vars, ty) -> begin
(

let uu____148 = (

let uu____149 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____150 = (

let uu____151 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____151 (FStar_String.concat ", ")))
in (

let uu____160 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____161 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____149 uu____150 uu____160 uu____161)))))
in (fail t.FStar_Syntax_Syntax.pos uu____148))
end))


let err_ill_typed_application = (fun env t args ty -> (

let uu____198 = (

let uu____199 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____200 = (

let uu____201 = (FStar_All.pipe_right args (FStar_List.map (fun uu____212 -> (match (uu____212) with
| (x, uu____216) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____201 (FStar_String.concat " ")))
in (

let uu____218 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" uu____199 uu____200 uu____218))))
in (fail t.FStar_Syntax_Syntax.pos uu____198)))


let err_value_restriction = (fun t -> (

let uu____232 = (

let uu____233 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____234 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____233 uu____234)))
in (fail t.FStar_Syntax_Syntax.pos uu____232)))


let err_unexpected_eff = (fun t f0 f1 -> (

let uu____260 = (

let uu____261 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" uu____261 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos uu____260)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____277 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____277) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____281 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____281) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____287, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (match ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____295 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____296 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____309 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____309) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____311 -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end
| FStar_Pervasives_Native.None -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end)
end)))))


let rec is_arity : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let uu____324 = (

let uu____325 = (FStar_Syntax_Subst.compress t1)
in uu____325.FStar_Syntax_Syntax.n)
in (match (uu____324) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____328) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____343) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____361) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____366) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____377) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____378) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____379) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____380) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____381, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____393) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____395 = (

let uu____396 = (FStar_Syntax_Subst.compress t2)
in uu____396.FStar_Syntax_Syntax.n)
in (match (uu____395) with
| FStar_Syntax_Syntax.Tm_fvar (uu____399) -> begin
false
end
| uu____400 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____401) -> begin
(

let uu____411 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____411) with
| (head1, uu____422) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____438) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____444) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____449, body, uu____451) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____464, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____476, branches) -> begin
(match (branches) with
| ((uu____502, uu____503, e))::uu____505 -> begin
(is_arity env e)
end
| uu____537 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____557) -> begin
(

let uu____572 = (

let uu____573 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____573))
in (failwith uu____572))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____574 = (

let uu____575 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____575))
in (failwith uu____574))
end
| FStar_Syntax_Syntax.Tm_constant (uu____576) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____577) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____578) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____583) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____593 = (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____593) with
| true -> begin
true
end
| uu____594 -> begin
(

let uu____595 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____595) with
| ((us, t2), uu____602) -> begin
((FStar_Extraction_ML_UEnv.debug env (fun uu____610 -> (

let uu____611 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____612 = (

let uu____613 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_All.pipe_right uu____613 (FStar_String.concat ", ")))
in (

let uu____616 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "Looked up type of %s; got <%s>.%s" uu____611 uu____612 uu____616))))));
(is_arity env t2);
)
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____617, t2) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____635; FStar_Syntax_Syntax.index = uu____636; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____640; FStar_Syntax_Syntax.index = uu____641; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____646, uu____647) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____677) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____684) -> begin
(

let uu____697 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____697) with
| (uu____700, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____713 = (

let uu____716 = (

let uu____717 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____717)::[])
in (FStar_Syntax_Subst.open_term uu____716 body))
in (match (uu____713) with
| (uu____718, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____720, lbs), body) -> begin
(

let uu____732 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____732) with
| (uu____736, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____740, branches) -> begin
(match (branches) with
| (b)::uu____767 -> begin
(

let uu____796 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____796) with
| (uu____797, uu____798, e) -> begin
(is_type_aux env e)
end))
end
| uu____812 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____824) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____830) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____857 -> (

let uu____858 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____859 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____858 uu____859)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____865 -> (match (b) with
| true -> begin
(

let uu____866 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____867 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____866 uu____867)))
end
| uu____868 -> begin
(

let uu____869 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____870 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____869 uu____870)))
end)));
b;
));
))


let is_type_binder = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____894 = (

let uu____895 = (FStar_Syntax_Subst.compress t)
in uu____895.FStar_Syntax_Syntax.n)
in (match (uu____894) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____898; FStar_Syntax_Syntax.fv_delta = uu____899; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____900; FStar_Syntax_Syntax.fv_delta = uu____901; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____902))}) -> begin
true
end
| uu____906 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____911 = (

let uu____912 = (FStar_Syntax_Subst.compress t)
in uu____912.FStar_Syntax_Syntax.n)
in (match (uu____911) with
| FStar_Syntax_Syntax.Tm_constant (uu____915) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____916) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____917) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____918) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____944 = (is_constructor head1)
in (match (uu____944) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____955 -> (match (uu____955) with
| (te, uu____959) -> begin
(is_fstar_value te)
end))))
end
| uu____960 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____962) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____968, uu____969) -> begin
(is_fstar_value t1)
end
| uu____998 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1003) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1004) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1005) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1006) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1012, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1018, fields) -> begin
(FStar_Util.for_all (fun uu____1033 -> (match (uu____1033) with
| (uu____1036, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| uu____1038 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1079 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1081 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1081) with
| true -> begin
(aux bs e' copt)
end
| uu____1082 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1085 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1085))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match (((FStar_List.length l) <> (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1131 -> begin
(

let uu____1132 = (FStar_List.hd l)
in (match (uu____1132) with
| (p1, w1, e1) -> begin
(

let uu____1151 = (

let uu____1156 = (FStar_List.tl l)
in (FStar_List.hd uu____1156))
in (match (uu____1151) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1195 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1247 = (erasable g f ty)
in (match (uu____1247) with
| true -> begin
(

let uu____1248 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1248) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1249 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1250 -> begin
e
end))
in ((e1), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1268 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____1268) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____1274 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1283 -> (

let uu____1284 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1285 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1286 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1284 uu____1285 uu____1286))))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1295 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1295) with
| FStar_Util.Inl (uu____1296, t) -> begin
t
end
| uu____1304 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1340) -> begin
(

let uu____1344 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1344) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____1347 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1350 = (is_top_ty mlt)
in (match (uu____1350) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1352 -> begin
mlt
end))))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____1356) -> begin
(

let uu____1357 = (

let uu____1358 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1358))
in (failwith uu____1357))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1359) -> begin
(

let uu____1374 = (

let uu____1375 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1375))
in (failwith uu____1374))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____1376 = (

let uu____1377 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1377))
in (failwith uu____1376))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1378) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1379) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1391) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____1396; FStar_Syntax_Syntax.index = uu____1397; FStar_Syntax_Syntax.sort = t2}, uu____1399) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1407) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1413, uu____1414) -> begin
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

let uu____1461 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1461) with
| (bs1, c1) -> begin
(

let uu____1466 = (binders_as_ml_binders env bs1)
in (match (uu____1466) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____1482 = (

let uu____1486 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____1486))
in (match (uu____1482) with
| (ed, qualifiers) -> begin
(

let uu____1498 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____1498) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____1502 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____1504 = (FStar_List.fold_right (fun uu____1517 uu____1518 -> (match (((uu____1517), (uu____1518))) with
| ((uu____1529, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____1504) with
| (uu____1537, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____1556 = (

let uu____1557 = (FStar_Syntax_Util.un_uinst head1)
in uu____1557.FStar_Syntax_Syntax.n)
in (match (uu____1556) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____1578 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____1578))
end
| uu____1594 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____1597) -> begin
(

let uu____1610 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____1610) with
| (bs1, ty1) -> begin
(

let uu____1615 = (binders_as_ml_binders env bs1)
in (match (uu____1615) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____1629) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_let (uu____1630) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____1638) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____1654 -> (match (uu____1654) with
| (a, uu____1658) -> begin
(

let uu____1659 = (is_type g a)
in (match (uu____1659) with
| true -> begin
(term_as_mlty' g a)
end
| uu____1660 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____1664 = (

let uu____1672 = (FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1672) with
| ((uu____1684, ty), uu____1686) -> begin
(FStar_Syntax_Util.arrow_formals ty)
end))
in (match (uu____1664) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____1727 = (FStar_Util.first_N n_args formals)
in (match (uu____1727) with
| (uu____1743, rest) -> begin
(

let uu____1757 = (FStar_List.map (fun uu____1762 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____1757))
end))
end
| uu____1765 -> begin
mlargs
end))
in (

let nm = (

let uu____1767 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____1767) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____1778 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1810 b -> (match (uu____1810) with
| (ml_bs, env) -> begin
(

let uu____1840 = (is_type_binder g b)
in (match (uu____1840) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____1855 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____1855), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____1869 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____1872 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____1872) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____1890 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____1890), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____1778) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____1952) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____1954, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____1957 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(match ((body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr)) with
| true -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1980 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1982 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____1983 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____1984 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____1986 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____2001 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____2001) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____2004 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____2020 -> begin
p
end)
end))
end
| uu____2022 -> begin
p
end))


let rec extract_one_pat : Prims.bool  ->  FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.list) FStar_Pervasives_Native.option * Prims.bool) = (fun imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let ok = (type_leq g t t')
in ((match ((not (ok))) with
| true -> begin
(FStar_Extraction_ML_UEnv.debug g (fun uu____2065 -> (

let uu____2066 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____2067 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____2066 uu____2067)))))
end
| uu____2068 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, FStar_Pervasives_Native.None)) -> begin
(

let i = FStar_Const.Const_int (((c), (FStar_Pervasives_Native.None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____2090 = (

let uu____2091 = (

let uu____2095 = (

let uu____2097 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____2098 = (

let uu____2100 = (

let uu____2101 = (

let uu____2102 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_41 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_41)) uu____2102))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____2101))
in (uu____2100)::[])
in (uu____2097)::uu____2098))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____2095)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2091))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2090))
in (

let uu____2104 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____2104))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____2116 = (

let uu____2121 = (

let uu____2125 = (

let uu____2126 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____2126))
in ((uu____2125), ([])))
in FStar_Pervasives_Native.Some (uu____2121))
in (

let uu____2131 = (ok mlty)
in ((g), (uu____2116), (uu____2131))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____2138 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____2138) with
| (g1, x1) -> begin
(

let uu____2151 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2163 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____2151)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____2170 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____2170) with
| (g1, x1) -> begin
(

let uu____2183 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2195 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____2183)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____2200) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____2222 = (

let uu____2225 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____2225) with
| FStar_Util.Inr (uu____2228, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____2230; FStar_Extraction_ML_Syntax.loc = uu____2231}, ttys, uu____2233) -> begin
((n1), (ttys))
end
| uu____2240 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____2222) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____2255 = (FStar_Util.first_N nTyVars pats)
in (match (uu____2255) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____2331 -> (match (uu____2331) with
| (p1, uu____2336) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2339, t) -> begin
(term_as_mlty g t)
end
| uu____2345 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2349 -> (

let uu____2350 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____2350))));
(FStar_Pervasives.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____2352 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____2352))))
end)
with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end
in (

let uu____2368 = (FStar_Util.fold_map (fun g1 uu____2391 -> (match (uu____2391) with
| (p1, imp1) -> begin
(

let uu____2402 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None)
in (match (uu____2402) with
| (g2, p2, uu____2418) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____2368) with
| (g1, tyMLPats) -> begin
(

let uu____2450 = (FStar_Util.fold_map (fun uu____2489 uu____2490 -> (match (((uu____2489), (uu____2490))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____2539 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____2571 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____2539) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____2608 = (extract_one_pat false g2 p1 expected_ty)
in (match (uu____2608) with
| (g3, p2, uu____2630) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____2450) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____2691 = (

let uu____2697 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___138_2724 -> (match (uu___138_2724) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____2746 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2697 FStar_List.split))
in (match (uu____2691) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____2785 -> begin
false
end)
in (

let uu____2790 = (

let uu____2795 = (

let uu____2799 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____2801 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____2799), (uu____2801))))
in FStar_Pervasives_Native.Some (uu____2795))
in ((g2), (uu____2790), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____2858 = (extract_one_pat false g1 p1 expected_t1)
in (match (uu____2858) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____2889 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____2914 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____2914))
end))
in (

let uu____2915 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____2915) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____3001, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____3004 = (

let uu____3010 = (

let uu____3015 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____3015)))
in (uu____3010)::more_args)
in (eta_args uu____3004 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____3022, uu____3023) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____3035 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____3053, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____3072 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____3085 = (eta_args [] residualType)
in (match (uu____3085) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____3113 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____3113))
end
| uu____3114 -> begin
(

let uu____3120 = (FStar_List.unzip eargs)
in (match (uu____3120) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____3144 = (

let uu____3145 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____3145))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____3144))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____3150 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____3152, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3155; FStar_Extraction_ML_Syntax.loc = uu____3156}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____3174 -> begin
(

let uu____3176 = (

let uu____3180 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____3180), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3176))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3183; FStar_Extraction_ML_Syntax.loc = uu____3184}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____3189 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3189))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3192; FStar_Extraction_ML_Syntax.loc = uu____3193}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____3195))) -> begin
(

let uu____3202 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3202))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____3206 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3206))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____3209))) -> begin
(

let uu____3214 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3214))
end
| uu____3216 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____3232 = ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____3232) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____3233 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____3273 = (term_as_mlexpr' g t)
in (match (uu____3273) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3288 = (

let uu____3289 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3290 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____3291 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____3289 uu____3290 uu____3291 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____3288))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____3298 = (check_term_as_mlexpr' g t f ty)
in (match (uu____3298) with
| (e, t1) -> begin
(

let uu____3305 = (erase g e t1 f)
in (match (uu____3305) with
| (r, uu____3312, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____3320 = (term_as_mlexpr g e0)
in (match (uu____3320) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____3332 = (maybe_coerce g e t ty)
in ((uu____3332), (ty)))
end
| uu____3333 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3345 = (

let uu____3346 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3347 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____3348 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____3346 uu____3347 uu____3348))))
in (FStar_Util.print_string uu____3345))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3353 = (

let uu____3354 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3354))
in (failwith uu____3353))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3358) -> begin
(

let uu____3373 = (

let uu____3374 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3374))
in (failwith uu____3373))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3378) -> begin
(

let uu____3389 = (

let uu____3390 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3390))
in (failwith uu____3389))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3394) -> begin
(

let uu____3395 = (

let uu____3396 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3396))
in (failwith uu____3395))
end
| FStar_Syntax_Syntax.Tm_type (uu____3400) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____3401) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3406) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____3419 = (term_as_mlexpr' g t1)
in (match (uu____3419) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____3446 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____3455)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____3478 = (

let uu____3482 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____3482))
in (match (uu____3478) with
| (ed, qualifiers) -> begin
(

let uu____3497 = (

let uu____3498 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____3498 Prims.op_Negation))
in (match (uu____3497) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____3503 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____3507 -> begin
(term_as_mlexpr' g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____3509) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3515) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3521 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____3521) with
| (uu____3528, ty, uu____3530) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____3532 = (

let uu____3533 = (

let uu____3534 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_42)) uu____3534))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3533))
in ((uu____3532), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____3535) -> begin
(

let uu____3536 = (is_type g t)
in (match (uu____3536) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3540 -> begin
(

let uu____3541 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3541) with
| (FStar_Util.Inl (uu____3548), uu____3549) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____3568, x, mltys, uu____3571), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____3596 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____3596), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____3597 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3601) -> begin
(

let uu____3602 = (is_type g t)
in (match (uu____3602) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3606 -> begin
(

let uu____3607 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3607) with
| (FStar_Util.Inl (uu____3614), uu____3615) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____3634, x, mltys, uu____3637), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____3662 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____3662), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____3663 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____3682 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3682) with
| (bs1, body1) -> begin
(

let uu____3690 = (binders_as_ml_binders g bs1)
in (match (uu____3690) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____3709 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____3709) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____3710 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3714 -> (

let uu____3715 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____3715))));
body1;
)
end)
in (

let uu____3716 = (term_as_mlexpr env body2)
in (match (uu____3716) with
| (ml_body, f, t1) -> begin
(

let uu____3726 = (FStar_List.fold_right (fun uu____3739 uu____3740 -> (match (((uu____3739), (uu____3740))) with
| ((uu____3751, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____3726) with
| (f1, tfun) -> begin
(

let uu____3764 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____3764), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3768)); FStar_Syntax_Syntax.tk = uu____3769; FStar_Syntax_Syntax.pos = uu____3770; FStar_Syntax_Syntax.vars = uu____3771}, uu____3772) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____3791)::((v1, uu____3793))::[]) when ((FStar_Syntax_Util.is_fstar_tactics_embed head1) && false) -> begin
(

let uu____3823 = (

let uu____3826 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.format2 "Trying to extract a quotation of %s" uu____3826))
in (

let s = (

let uu____3828 = (

let uu____3829 = (

let uu____3830 = (

let uu____3832 = (FStar_Util.marshal v1)
in (FStar_Util.bytes_of_string uu____3832))
in FStar_Extraction_ML_Syntax.MLC_Bytes (uu____3830))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____3829))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty uu____3828))
in (

let zero1 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int ((("0"), (FStar_Pervasives_Native.None))))))
in (

let term_ty = (

let uu____3842 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.fstar_syntax_syntax_term FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (term_as_mlty g uu____3842))
in (

let marshal_from_string = (

let string_to_term_ty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_string_ty), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty)))
in (FStar_Extraction_ML_Syntax.with_ty string_to_term_ty (FStar_Extraction_ML_Syntax.MLE_Name (((("Marshal")::[]), ("from_string"))))))
in (

let uu____3846 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty) (FStar_Extraction_ML_Syntax.MLE_App (((marshal_from_string), ((s)::(zero1)::[])))))
in ((uu____3846), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty))))))))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___139_3870 -> (match (uu___139_3870) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3871 -> begin
false
end))))))
in (

let uu____3872 = (

let uu____3875 = (

let uu____3876 = (FStar_Syntax_Subst.compress head1)
in uu____3876.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____3875)))
in (match (uu____3872) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____3882), uu____3883) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____3895, FStar_Syntax_Syntax.Tm_abs (bs, uu____3897, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____3911, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____3913 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____3913))
in (

let tm = (

let uu____3921 = (

let uu____3922 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____3923 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3922 uu____3923)))
in (uu____3921 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr' g tm)))
end
| uu____3932 -> begin
(

let rec extract_app = (fun is_data uu____3960 uu____3961 restArgs -> (match (((uu____3960), (uu____3961))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____4009) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____4026 -> begin
false
end))
in (

let uu____4027 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____4040 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (([]), (uu____4040)))
end
| uu____4056 -> begin
(FStar_List.fold_left (fun uu____4071 uu____4072 -> (match (((uu____4071), (uu____4072))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((f1 = FStar_Extraction_ML_Syntax.E_PURE) || (f1 = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____4125 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____4127 = (

let uu____4129 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____4129)::out_args)
in (((((x), (arg)))::lbs), (uu____4127))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____4027) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____4156 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____4156))
in (

let l_app = (FStar_List.fold_right (fun uu____4165 out -> (match (uu____4165) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____4178))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____4196 = (

let uu____4199 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____4199), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____4196 rest))
end
| (((e0, uu____4206))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____4225 = (term_as_mlexpr g e0)
in (match (uu____4225) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____4236 = (

let uu____4239 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____4239), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____4236 rest)))
end)))
end
| uu____4245 -> begin
(

let uu____4252 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____4252) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____4288 args1 -> (match (uu____4288) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____4307)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4357))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4359, f', t3)) -> begin
(

let uu____4384 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____4384 t3))
end
| uu____4385 -> begin
((args2), (f1), (t2))
end))
in (

let uu____4400 = (remove_implicits args1 f t1)
in (match (uu____4400) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____4433 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____4440 = (is_type g t)
in (match (uu____4440) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____4444 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid) && (

let uu____4451 = (

let uu____4452 = (FStar_Extraction_ML_Syntax.string_of_mlpath g.FStar_Extraction_ML_UEnv.currentModule)
in (uu____4452 = "FStar.Tactics.Builtins"))
in (not (uu____4451)))) -> begin
(match (args) with
| (a)::(b)::[] -> begin
(term_as_mlexpr g (FStar_Pervasives_Native.fst a))
end
| uu____4480 -> begin
(

let uu____4486 = (FStar_Syntax_Print.args_to_string args)
in (failwith uu____4486))
end)
end
| FStar_Syntax_Syntax.Tm_name (uu____4490) -> begin
(

let uu____4491 = (

let uu____4498 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____4498) with
| (FStar_Util.Inr (uu____4508, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____4533 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4491) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4562))::uu____4563 -> begin
(is_type g a)
end
| uu____4577 -> begin
false
end)
in (

let uu____4583 = (match (vars) with
| (uu____4600)::uu____4601 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____4608 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____4634 = (FStar_Util.first_N n1 args)
in (match (uu____4634) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4692 -> (match (uu____4692) with
| (x, uu____4696) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____4699) -> begin
(

let uu___143_4700 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4700.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4700.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____4701) -> begin
(

let uu___143_4702 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4702.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4702.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4704; FStar_Extraction_ML_Syntax.loc = uu____4705})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___144_4709 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___144_4709.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___144_4709.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____4710 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____4716 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____4583) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____4748 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____4748), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____4749 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4755) -> begin
(

let uu____4756 = (

let uu____4763 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____4763) with
| (FStar_Util.Inr (uu____4773, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____4798 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4756) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4827))::uu____4828 -> begin
(is_type g a)
end
| uu____4842 -> begin
false
end)
in (

let uu____4848 = (match (vars) with
| (uu____4865)::uu____4866 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____4873 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____4899 = (FStar_Util.first_N n1 args)
in (match (uu____4899) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4957 -> (match (uu____4957) with
| (x, uu____4961) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____4964) -> begin
(

let uu___143_4965 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4965.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4965.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____4966) -> begin
(

let uu___143_4967 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4967.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4967.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4969; FStar_Extraction_ML_Syntax.loc = uu____4970})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___144_4974 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___144_4974.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___144_4974.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____4975 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____4981 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____4848) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____5013 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____5013), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____5014 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____5020 -> begin
(

let uu____5021 = (term_as_mlexpr g head2)
in (match (uu____5021) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____5033), f) -> begin
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
| FStar_Pervasives_Native.None -> begin
(failwith "Ascription node with an empty effect label")
end
| FStar_Pervasives_Native.Some (l) -> begin
(effect_as_etag g l)
end)
in (

let uu____5087 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____5087) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____5108 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____5115 -> begin
(

let uu____5116 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5116) with
| true -> begin
((lbs), (e'))
end
| uu____5123 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____5126 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____5126))
in (

let lb1 = (

let uu___145_5128 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___145_5128.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___145_5128.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___145_5128.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___145_5128.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____5108) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____5150 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____5150))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____5155 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____5159 = (FStar_Options.ml_ish ())
in (match (uu____5159) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____5162 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___146_5163 = lb
in {FStar_Syntax_Syntax.lbname = uu___146_5163.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_5163.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_5163.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_5163.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____5164 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____5177 -> (match (uu____5177) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____5188; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____5231 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____5231 (is_type_binder g))) -> begin
(

let uu____5238 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5238) with
| (bs1, c1) -> begin
(

let uu____5252 = (

let uu____5257 = (FStar_Util.prefix_until (fun x -> (

let uu____5277 = (is_type_binder g x)
in (not (uu____5277)))) bs1)
in (match (uu____5257) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____5325 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____5325)))
end))
in (match (uu____5252) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____5356 = (normalize_abs e)
in (FStar_All.pipe_right uu____5356 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____5381 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____5381) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____5416 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____5416) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____5468 uu____5469 -> (match (((uu____5468), (uu____5469))) with
| ((x, uu____5479), (y, uu____5481)) -> begin
(

let uu____5486 = (

let uu____5491 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____5491)))
in FStar_Syntax_Syntax.NT (uu____5486))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____5500 -> (match (uu____5500) with
| (a, uu____5504) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____5512 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____5529 -> (match (uu____5529) with
| (x, uu____5535) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5512), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____5542 = (is_fstar_value body1)
in (not (uu____5542)))
end
| uu____5543 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____5550 -> begin
rest_args
end)
in (

let body2 = (match (rest_args1) with
| [] -> begin
body1
end
| uu____5552 -> begin
(FStar_Syntax_Util.abs rest_args1 body1 copt)
end)
in ((lbname_), (f_e), (((t2), (((targs), (polytype))))), (add_unit), (body2)))))))))
end))
end
| uu____5586 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____5596) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5609 -> (match (uu____5609) with
| (a, uu____5613) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5621 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5635 -> (match (uu____5635) with
| (x, uu____5641) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5621), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5654 -> (match (uu____5654) with
| (bv, uu____5658) -> begin
(

let uu____5659 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5659 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5693) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5702 -> (match (uu____5702) with
| (a, uu____5706) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5714 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5728 -> (match (uu____5728) with
| (x, uu____5734) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5714), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5747 -> (match (uu____5747) with
| (bv, uu____5751) -> begin
(

let uu____5752 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5752 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____5786) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5795 -> (match (uu____5795) with
| (a, uu____5799) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5807 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5821 -> (match (uu____5821) with
| (x, uu____5827) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5807), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5840 -> (match (uu____5840) with
| (bv, uu____5844) -> begin
(

let uu____5845 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5845 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____5879 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____5889 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____5946 -> (match (uu____5946) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____6021 -> (match (uu____6021) with
| (a, uu____6025) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((FStar_Pervasives_Native.snd polytype))))
end
| uu____6027 -> begin
(FStar_Pervasives_Native.snd polytype)
end)
in (

let uu____6028 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____6028) with
| (e1, uu____6034) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____6069 = (FStar_List.fold_right (fun lb uu____6123 -> (match (uu____6123) with
| (env, lbs4) -> begin
(

let uu____6187 = lb
in (match (uu____6187) with
| (lbname, uu____6212, (t1, (uu____6214, polytype)), add_unit, uu____6217) -> begin
(

let uu____6224 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____6224) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____6069) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____6328 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____6367 = (term_as_mlexpr env_body e'1)
in (match (uu____6367) with
| (e'2, f', t') -> begin
(

let f = (

let uu____6378 = (

let uu____6380 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____6380)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____6378))
in (

let is_rec1 = (match ((is_rec = true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____6385 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____6386 = (

let uu____6387 = (

let uu____6388 = (

let uu____6389 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), ([]), (uu____6389)))
in (mk_MLE_Let top_level uu____6388 e'2))
in (

let uu____6395 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____6387 uu____6395)))
in ((uu____6386), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____6422 = (term_as_mlexpr g scrutinee)
in (match (uu____6422) with
| (e, f_e, t_e) -> begin
(

let uu____6432 = (check_pats_for_ite pats)
in (match (uu____6432) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____6467 = (term_as_mlexpr g then_e1)
in (match (uu____6467) with
| (then_mle, f_then, t_then) -> begin
(

let uu____6477 = (term_as_mlexpr g else_e1)
in (match (uu____6477) with
| (else_mle, f_else, t_else) -> begin
(

let uu____6487 = (

let uu____6494 = (type_leq g t_then t_else)
in (match (uu____6494) with
| true -> begin
((t_else), (no_lift))
end
| uu____6505 -> begin
(

let uu____6506 = (type_leq g t_else t_then)
in (match (uu____6506) with
| true -> begin
((t_then), (no_lift))
end
| uu____6517 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____6487) with
| (t_branch, maybe_lift1) -> begin
(

let uu____6535 = (

let uu____6536 = (

let uu____6537 = (

let uu____6542 = (maybe_lift1 then_mle t_then)
in (

let uu____6543 = (

let uu____6545 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____6545))
in ((e), (uu____6542), (uu____6543))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____6537))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____6536))
in (

let uu____6547 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____6535), (uu____6547), (t_branch))))
end))
end))
end))
end
| uu____6548 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____6556 -> begin
(

let uu____6557 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____6624 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____6624) with
| (pat, when_opt, branch1) -> begin
(

let uu____6652 = (extract_pat g pat t_e)
in (match (uu____6652) with
| (env, p, pat_t_compat) -> begin
(

let uu____6683 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____6698 = (term_as_mlexpr env w)
in (match (uu____6698) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end))
end)
in (match (uu____6683) with
| (when_opt1, f_when) -> begin
(

let uu____6726 = (term_as_mlexpr env branch1)
in (match (uu____6726) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____6745 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6786 -> (match (uu____6786) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____6745)))
end))
end))
end))
end))) true))
in (match (uu____6557) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____6870 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____6875 -> (

let uu____6876 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____6877 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____6876 uu____6877)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____6890 = (

let uu____6895 = (

let uu____6904 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____6904))
in (FStar_All.pipe_left FStar_Util.right uu____6895))
in (match (uu____6890) with
| (uu____6926, fw, uu____6928, uu____6929) -> begin
(

let uu____6930 = (

let uu____6931 = (

let uu____6932 = (

let uu____6936 = (

let uu____6938 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____6938)::[])
in ((fw), (uu____6936)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6932))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____6931))
in ((uu____6930), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____6940, uu____6941, (uu____6942, f_first, t_first)))::rest -> begin
(

let uu____6974 = (FStar_List.fold_left (fun uu____7001 uu____7002 -> (match (((uu____7001), (uu____7002))) with
| ((topt, f), (uu____7032, uu____7033, (uu____7034, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____7065 = (type_leq g t1 t_branch)
in (match (uu____7065) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____7067 -> begin
(

let uu____7068 = (type_leq g t_branch t1)
in (match (uu____7068) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____7070 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____6974) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____7122 -> (match (uu____7122) with
| (p, (wopt, uu____7138), (b1, uu____7140, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____7151) -> begin
b1
end)
in ((p), (wopt), (b2)))
end))))
in (

let t_match = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (

let uu____7155 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____7155), (f_match), (t_match)))))
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

let uu____7174 = (FStar_ST.read c)
in ((x), (uu____7174)));
)))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____7189 = (

let uu____7192 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7192))
in (match (uu____7189) with
| (uu____7205, fstar_disc_type) -> begin
(

let wildcards = (

let uu____7213 = (

let uu____7214 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____7214.FStar_Syntax_Syntax.n)
in (match (uu____7213) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____7223) -> begin
(

let uu____7234 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___140_7252 -> (match (uu___140_7252) with
| (uu____7256, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7257))) -> begin
true
end
| uu____7259 -> begin
false
end))))
in (FStar_All.pipe_right uu____7234 (FStar_List.map (fun uu____7281 -> (

let uu____7285 = (fresh "_")
in ((uu____7285), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____7290 -> begin
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

let uu____7302 = (

let uu____7303 = (

let uu____7309 = (

let uu____7310 = (

let uu____7311 = (

let uu____7319 = (

let uu____7320 = (

let uu____7321 = (

let uu____7322 = (FStar_Extraction_ML_Syntax.idsym mlid)
in (([]), (uu____7322)))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____7321))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) uu____7320))
in (

let uu____7324 = (

let uu____7330 = (

let uu____7335 = (

let uu____7336 = (

let uu____7340 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____7340), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____7336))
in (

let uu____7342 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____7335), (FStar_Pervasives_Native.None), (uu____7342))))
in (

let uu____7344 = (

let uu____7350 = (

let uu____7355 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____7355)))
in (uu____7350)::[])
in (uu____7330)::uu____7344))
in ((uu____7319), (uu____7324))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____7311))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____7310))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____7309)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____7303))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____7302))
in (

let uu____7393 = (

let uu____7394 = (

let uu____7396 = (

let uu____7397 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____7397; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____7396)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____7394)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____7393)))))))
end)))




