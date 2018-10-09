
open Prims
open FStar_Pervasives
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____6 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields : 'Auu____68 . FStar_Ident.ident Prims.list  ->  'Auu____68 Prims.list  ->  (Prims.string * 'Auu____68) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail : 'Auu____107 . FStar_Range.range  ->  (FStar_Errors.raw_error * Prims.string)  ->  'Auu____107 = (fun r err -> (FStar_Errors.raise_error err r))


let err_uninst : 'Auu____136 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Syntax_Syntax.term  ->  'Auu____136 = (fun env t uu____161 app -> (match (uu____161) with
| (vars, ty) -> begin
(

let uu____175 = (

let uu____180 = (

let uu____181 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____182 = (FStar_All.pipe_right vars (FStar_String.concat ", "))
in (

let uu____185 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____186 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____181 uu____182 uu____185 uu____186)))))
in ((FStar_Errors.Fatal_Uninstantiated), (uu____180)))
in (fail t.FStar_Syntax_Syntax.pos uu____175))
end))


let err_ill_typed_application : 'Auu____201 'Auu____202 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  (FStar_Syntax_Syntax.term * 'Auu____201) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____202 = (fun env t mlhead args ty -> (

let uu____240 = (

let uu____245 = (

let uu____246 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____247 = (FStar_Extraction_ML_Code.string_of_mlexpr env.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (

let uu____248 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____249 = (

let uu____250 = (FStar_All.pipe_right args (FStar_List.map (fun uu____268 -> (match (uu____268) with
| (x, uu____274) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____250 (FStar_String.concat " ")))
in (FStar_Util.format4 "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n" uu____246 uu____247 uu____248 uu____249)))))
in ((FStar_Errors.Fatal_IllTyped), (uu____245)))
in (fail t.FStar_Syntax_Syntax.pos uu____240)))


let err_ill_typed_erasure : 'Auu____285 . FStar_Extraction_ML_UEnv.env  ->  FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____285 = (fun env pos ty -> (

let uu____301 = (

let uu____306 = (

let uu____307 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format1 "Erased value found where a value of type %s was expected" uu____307))
in ((FStar_Errors.Fatal_IllTyped), (uu____306)))
in (fail pos uu____301)))


let err_value_restriction : 'Auu____312 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____312 = (fun t -> (

let uu____322 = (

let uu____327 = (

let uu____328 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____329 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____328 uu____329)))
in ((FStar_Errors.Fatal_ValueRestriction), (uu____327)))
in (fail t.FStar_Syntax_Syntax.pos uu____322)))


let err_unexpected_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  unit = (fun env t ty f0 f1 -> (

let uu____359 = (

let uu____364 = (

let uu____365 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____366 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____367 = (FStar_Extraction_ML_Util.eff_to_string f0)
in (

let uu____368 = (FStar_Extraction_ML_Util.eff_to_string f1)
in (FStar_Util.format4 "for expression %s of type %s, Expected effect %s; got effect %s" uu____365 uu____366 uu____367 uu____368)))))
in ((FStar_Errors.Warning_ExtractionUnexpectedEffect), (uu____364)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____359)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____391 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____391) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____396 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____396) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____407, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (

let uu____417 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)
in (match (uu____417) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____418 -> begin
(

let uu____419 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____419) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____420 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____442 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____442) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____443 -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end
| FStar_Pervasives_Native.None -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end))
end))))))


let rec is_arity : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let uu____461 = (

let uu____462 = (FStar_Syntax_Subst.compress t1)
in uu____462.FStar_Syntax_Syntax.n)
in (match (uu____461) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____465) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____488) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____515) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____523 = (FStar_Syntax_Util.unfold_lazy i)
in (is_arity env uu____523))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____524) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____537) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____538) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____539) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____546) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____547) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____548, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____570) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____572 = (

let uu____573 = (FStar_Syntax_Subst.compress t2)
in uu____573.FStar_Syntax_Syntax.n)
in (match (uu____572) with
| FStar_Syntax_Syntax.Tm_fvar (uu____576) -> begin
false
end
| uu____577 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____578) -> begin
(

let uu____595 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____595) with
| (head1, uu____613) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____639) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____645) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____650, body, uu____652) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____677, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____695, branches) -> begin
(match (branches) with
| ((uu____733, uu____734, e))::uu____736 -> begin
(is_arity env e)
end
| uu____783 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____811) -> begin
(

let uu____834 = (

let uu____835 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____835))
in (failwith uu____834))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____836 = (

let uu____837 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____837))
in (failwith uu____836))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____839 = (FStar_Syntax_Util.unfold_lazy i)
in (is_type_aux env uu____839))
end
| FStar_Syntax_Syntax.Tm_constant (uu____840) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____841) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____842) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____849) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uu____866; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____867; FStar_Syntax_Syntax.ctx_uvar_binders = uu____868; FStar_Syntax_Syntax.ctx_uvar_typ = t2; FStar_Syntax_Syntax.ctx_uvar_reason = uu____870; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____871; FStar_Syntax_Syntax.ctx_uvar_range = uu____872}, s) -> begin
(

let uu____912 = (FStar_Syntax_Subst.subst' s t2)
in (is_arity env uu____912))
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____913; FStar_Syntax_Syntax.index = uu____914; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____918; FStar_Syntax_Syntax.index = uu____919; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____924, uu____925) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____967) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____974) -> begin
(

let uu____999 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____999) with
| (uu____1004, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1021 = (

let uu____1026 = (

let uu____1027 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1027)::[])
in (FStar_Syntax_Subst.open_term uu____1026 body))
in (match (uu____1021) with
| (uu____1046, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1048, lbs), body) -> begin
(

let uu____1065 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____1065) with
| (uu____1072, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____1078, branches) -> begin
(match (branches) with
| (b)::uu____1117 -> begin
(

let uu____1162 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____1162) with
| (uu____1163, uu____1164, e) -> begin
(is_type_aux env e)
end))
end
| uu____1182 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1199) -> begin
false
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1207) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1213) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1252 -> (

let uu____1253 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1254 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1253 uu____1254)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1260 -> (match (b) with
| true -> begin
(

let uu____1261 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1262 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____1261 uu____1262)))
end
| uu____1263 -> begin
(

let uu____1264 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1265 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1264 uu____1265)))
end)));
b;
));
))


let is_type_binder : 'Auu____1272 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____1272)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1296 = (

let uu____1297 = (FStar_Syntax_Subst.compress t)
in uu____1297.FStar_Syntax_Syntax.n)
in (match (uu____1296) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1300; FStar_Syntax_Syntax.fv_delta = uu____1301; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1302; FStar_Syntax_Syntax.fv_delta = uu____1303; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1304))}) -> begin
true
end
| uu____1311 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1317 = (

let uu____1318 = (FStar_Syntax_Subst.compress t)
in uu____1318.FStar_Syntax_Syntax.n)
in (match (uu____1317) with
| FStar_Syntax_Syntax.Tm_constant (uu____1321) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1322) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1323) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1324) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1369 = (is_constructor head1)
in (match (uu____1369) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1387 -> (match (uu____1387) with
| (te, uu____1395) -> begin
(is_fstar_value te)
end))))
end
| uu____1400 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1402) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1408, uu____1409) -> begin
(is_fstar_value t1)
end
| uu____1450 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1456) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1457) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1458) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1459) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1470, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1479, fields) -> begin
(FStar_Util.for_all (fun uu____1504 -> (match (uu____1504) with
| (uu____1509, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1512) -> begin
(is_ml_value h)
end
| uu____1517 -> begin
false
end))


let fresh : Prims.string  ->  Prims.string = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1560 = (

let uu____1561 = (FStar_ST.op_Bang c)
in (FStar_Util.string_of_int uu____1561))
in (Prims.strcat x uu____1560));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1682 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1684 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1684) with
| true -> begin
(aux bs e' copt)
end
| uu____1687 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1694 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1694))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1773 -> begin
(

let uu____1774 = (FStar_List.hd l)
in (match (uu____1774) with
| (p1, w1, e1) -> begin
(

let uu____1808 = (

let uu____1817 = (FStar_List.tl l)
in (FStar_List.hd uu____1817))
in (match (uu____1808) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1891 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____1928 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1928) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____1943 -> begin
(

let vs = (FStar_List.map (fun uu____1948 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____1959 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____1973 -> (match (uu____1973) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____1959))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let default_value_for_ty : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g t -> (

let uu____1999 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1999) with
| (ts, r) -> begin
(

let body = (fun r1 -> (

let r2 = (

let uu____2019 = (FStar_Extraction_ML_Util.udelta_unfold g r1)
in (match (uu____2019) with
| FStar_Pervasives_Native.None -> begin
r1
end
| FStar_Pervasives_Native.Some (r2) -> begin
r2
end))
in (match (r2) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr FStar_Extraction_ML_Syntax.ml_unit FStar_Extraction_ML_Syntax.MLTY_Erased)
end
| uu____2023 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased), (r2)))))
end)))
in (match ((Prims.op_Equality ts [])) with
| true -> begin
(body r)
end
| uu____2026 -> begin
(

let vs = (FStar_List.map (fun uu____2031 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let uu____2039 = (

let uu____2040 = (

let uu____2051 = (body r)
in ((vs_ts), (uu____2051)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____2040))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) uu____2039))))
end))
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____2068 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____2070 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____2070 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))))
in (match (uu____2068) with
| true -> begin
e
end
| uu____2075 -> begin
(eta_expand expect e)
end)))


let maybe_coerce : 'Auu____2088 . 'Auu____2088  ->  FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun pos g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____2115 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____2115) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____2125 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2137 -> (

let uu____2138 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____2139 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____2140 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____2138 uu____2139 uu____2140))))));
(match (ty1) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(default_value_for_ty g expect)
end
| uu____2141 -> begin
(

let uu____2142 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))))
in (maybe_eta_expand expect uu____2142))
end);
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____2153 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____2153) with
| FStar_Util.Inl (ty_b) -> begin
ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
end
| uu____2155 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let basic_norm_steps : FStar_TypeChecker_Env.step Prims.list = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]


let comp_no_args : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2171) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____2180) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let effect_args = (FStar_List.map (fun uu____2216 -> (match (uu____2216) with
| (uu____2231, aq) -> begin
((FStar_Syntax_Syntax.t_unit), (aq))
end)) ct.FStar_Syntax_Syntax.effect_args)
in (

let ct1 = (

let uu___368_2244 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___368_2244.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___368_2244.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___368_2244.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = uu___368_2244.FStar_Syntax_Syntax.flags})
in (

let c1 = (

let uu___369_2248 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___369_2248.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___369_2248.FStar_Syntax_Syntax.vars})
in c1)))
end))


let rec translate_term_to_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let arg_as_mlty = (fun g1 uu____2295 -> (match (uu____2295) with
| (a, uu____2303) -> begin
(

let uu____2308 = (is_type g1 a)
in (match (uu____2308) with
| true -> begin
(translate_term_to_mlty g1 a)
end
| uu____2309 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
in (

let fv_app_as_mlty = (fun g1 fv args -> (

let uu____2326 = (

let uu____2327 = (FStar_Extraction_ML_UEnv.is_fv_type g1 fv)
in (not (uu____2327)))
in (match (uu____2326) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| uu____2328 -> begin
(

let uu____2329 = (

let uu____2344 = (FStar_TypeChecker_Env.lookup_lid g1.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2344) with
| ((uu____2367, fvty), uu____2369) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) g1.FStar_Extraction_ML_UEnv.tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____2329) with
| (formals, uu____2376) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g1) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____2432 = (FStar_Util.first_N n_args formals)
in (match (uu____2432) with
| (uu____2465, rest) -> begin
(

let uu____2499 = (FStar_List.map (fun uu____2509 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____2499))
end))
end
| uu____2516 -> begin
mlargs
end))
in (

let nm = (

let uu____2518 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv)
in (match (uu____2518) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end))
end)))
in (

let aux = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____2536) -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2537) -> begin
(

let uu____2538 = (

let uu____2539 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2539))
in (failwith uu____2538))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2540) -> begin
(

let uu____2563 = (

let uu____2564 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2564))
in (failwith uu____2563))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2565 = (

let uu____2566 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2566))
in (failwith uu____2565))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2568 = (FStar_Syntax_Util.unfold_lazy i)
in (translate_term_to_mlty env uu____2568))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2569) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2570) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2577) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____2591) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____2596; FStar_Syntax_Syntax.index = uu____2597; FStar_Syntax_Syntax.sort = t2}, uu____2599) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2607) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2613, uu____2614) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv [])
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2687 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2687) with
| (bs1, c1) -> begin
(

let uu____2694 = (binders_as_ml_binders env bs1)
in (match (uu____2694) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let c2 = (comp_no_args c1)
in (

let uu____2724 = (

let uu____2731 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____2731))
in (match (uu____2724) with
| (ed, qualifiers) -> begin
(

let uu____2752 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____2752) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c2 FStar_Syntax_Syntax.U_unknown)
in ((FStar_Extraction_ML_UEnv.debug env1 (fun uu____2758 -> (

let uu____2759 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____2760 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Translating comp type %s as %s\n" uu____2759 uu____2760)))));
(

let res = (translate_term_to_mlty env1 t2)
in ((FStar_Extraction_ML_UEnv.debug env1 (fun uu____2767 -> (

let uu____2768 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____2769 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____2770 = (FStar_Extraction_ML_Code.string_of_mlty env1.FStar_Extraction_ML_UEnv.currentModule res)
in (FStar_Util.print3 "Translated comp type %s as %s ... to %s\n" uu____2768 uu____2769 uu____2770))))));
res;
));
))
end
| uu____2771 -> begin
(translate_term_to_mlty env1 (FStar_Syntax_Util.comp_result c2))
end))
end))))
in (

let erase = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2773 = (FStar_List.fold_right (fun uu____2792 uu____2793 -> (match (((uu____2792), (uu____2793))) with
| ((uu____2814, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (uu____2773) with
| (uu____2826, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____2855 = (

let uu____2856 = (FStar_Syntax_Util.un_uinst head1)
in uu____2856.FStar_Syntax_Syntax.n)
in (match (uu____2855) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____2887 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (translate_term_to_mlty env uu____2887))
end
| uu____2908 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2911) -> begin
(

let uu____2936 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____2936) with
| (bs1, ty1) -> begin
(

let uu____2943 = (binders_as_ml_binders env bs1)
in (match (uu____2943) with
| (bts, env1) -> begin
(translate_term_to_mlty env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_let (uu____2968) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____2981) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
in (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____3010) -> begin
(

let uu____3017 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____3017) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____3021 -> begin
false
end))
in (

let uu____3022 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv t0)
in (match (uu____3022) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| uu____3023 -> begin
(

let mlt = (aux g t0)
in (

let uu____3025 = (is_top_ty mlt)
in (match (uu____3025) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::basic_norm_steps) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (aux g t))
end
| uu____3027 -> begin
mlt
end)))
end)))))))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____3040 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____3093 b -> (match (uu____3093) with
| (ml_bs, env) -> begin
(

let uu____3135 = (is_type_binder g b)
in (match (uu____3135) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____3157 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____3157), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____3168 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (translate_term_to_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____3173 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____3173) with
| (env1, b2, uu____3192) -> begin
(

let ml_b = (

let uu____3198 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____3198), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____3040) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize basic_norm_steps g.FStar_Extraction_ML_UEnv.tcenv t0)
in (translate_term_to_mlty g t)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____3281) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____3284, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____3288 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some ([], t) when (Prims.op_Equality t FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(match ((Prims.op_Equality body.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr)) with
| true -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____3312 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____3314 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____3315 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____3316 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____3325 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____3352 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____3352) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____3356 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____3383 -> begin
p
end)
end))
end
| uu____3386 -> begin
p
end))


let rec extract_one_pat : Prims.bool  ->  FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option  ->  (FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.list) FStar_Pervasives_Native.option * Prims.bool) = (fun imp g p expected_topt term_as_mlexpr -> (

let ok = (fun t -> (match (expected_topt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let ok = (type_leq g t t')
in ((match ((not (ok))) with
| true -> begin
(FStar_Extraction_ML_UEnv.debug g (fun uu____3478 -> (

let uu____3479 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____3480 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____3479 uu____3480)))))
end
| uu____3481 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, swopt)) when (

let uu____3510 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____3510 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))) -> begin
(

let uu____3515 = (match (swopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3528 = (

let uu____3529 = (

let uu____3530 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (((c), (FStar_Pervasives_Native.None)))))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____3530))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____3529))
in ((uu____3528), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end
| FStar_Pervasives_Native.Some (sw) -> begin
(

let source_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer g.FStar_Extraction_ML_UEnv.tcenv.FStar_TypeChecker_Env.dsenv c sw FStar_Range.dummyRange)
in (

let uu____3551 = (term_as_mlexpr g source_term)
in (match (uu____3551) with
| (mlterm, uu____3563, mlty) -> begin
((mlterm), (mlty))
end)))
end)
in (match (uu____3515) with
| (mlc, ml_ty) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____3583 = (

let uu____3584 = (

let uu____3591 = (

let uu____3594 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ml_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____3594)::(mlc)::[])
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____3591)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3584))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3583))
in (

let uu____3597 = (ok ml_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____3597)))))
end))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____3617 = (

let uu____3626 = (

let uu____3633 = (

let uu____3634 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____3634))
in ((uu____3633), ([])))
in FStar_Pervasives_Native.Some (uu____3626))
in (

let uu____3643 = (ok mlty)
in ((g), (uu____3617), (uu____3643))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3654 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3654) with
| (g1, x1, uu____3677) -> begin
(

let uu____3678 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3701 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3678)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3712 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3712) with
| (g1, x1, uu____3735) -> begin
(

let uu____3736 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3759 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3736)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____3768) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____3807 = (

let uu____3816 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____3816) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____3825; FStar_Extraction_ML_UEnv.exp_b_expr = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____3827; FStar_Extraction_ML_Syntax.loc = uu____3828}; FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____3830} -> begin
((n1), (ttys))
end
| uu____3835 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____3807) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____3869 = (FStar_Util.first_N nTyVars pats)
in (match (uu____3869) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___371_3969 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____3998 -> (match (uu____3998) with
| (p1, uu____4004) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____4005, t) -> begin
(term_as_mlty g t)
end
| uu____4011 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____4015 -> (

let uu____4016 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____4016))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____4018 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____4018))))
end)) (fun uu___370_4032 -> (match (uu___370_4032) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____4047 = (FStar_Util.fold_map (fun g1 uu____4083 -> (match (uu____4083) with
| (p1, imp1) -> begin
(

let uu____4102 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None term_as_mlexpr)
in (match (uu____4102) with
| (g2, p2, uu____4131) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____4047) with
| (g1, tyMLPats) -> begin
(

let uu____4192 = (FStar_Util.fold_map (fun uu____4256 uu____4257 -> (match (((uu____4256), (uu____4257))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____4350 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____4410 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____4350) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____4481 = (extract_one_pat false g2 p1 expected_ty term_as_mlexpr)
in (match (uu____4481) with
| (g3, p2, uu____4522) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____4192) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____4640 = (

let uu____4651 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___365_4702 -> (match (uu___365_4702) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____4744 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4651 FStar_List.split))
in (match (uu____4640) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____4817 -> begin
false
end)
in (

let uu____4826 = (

let uu____4835 = (

let uu____4842 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____4845 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____4842), (uu____4845))))
in FStar_Pervasives_Native.Some (uu____4835))
in ((g2), (uu____4826), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t term_as_mlexpr -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____4972 = (extract_one_pat false g1 p1 expected_t1 term_as_mlexpr)
in (match (uu____4972) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____5029 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____5074 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____5074))
end))
in (

let uu____5075 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____5075) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____5225, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____5228 = (

let uu____5239 = (

let uu____5248 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____5248)))
in (uu____5239)::more_args)
in (eta_args uu____5228 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____5261, uu____5262) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____5285 -> begin
(

let uu____5286 = (

let uu____5287 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr)
in (

let uu____5288 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.format2 "Impossible: Head type is not an arrow: (%s : %s)" uu____5287 uu____5288)))
in (failwith uu____5286))
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____5320, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____5352 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____5374 = (eta_args [] residualType)
in (match (uu____5374) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____5427 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____5427))
end
| uu____5428 -> begin
(

let uu____5439 = (FStar_List.unzip eargs)
in (match (uu____5439) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____5481 = (

let uu____5482 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____5482))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____5481))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____5491 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____5494, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5498; FStar_Extraction_ML_Syntax.loc = uu____5499}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____5520 -> begin
(

let uu____5523 = (

let uu____5530 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____5530), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5523))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5534; FStar_Extraction_ML_Syntax.loc = uu____5535}, uu____5536); FStar_Extraction_ML_Syntax.mlty = uu____5537; FStar_Extraction_ML_Syntax.loc = uu____5538}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____5563 -> begin
(

let uu____5566 = (

let uu____5573 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____5573), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5566))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5577; FStar_Extraction_ML_Syntax.loc = uu____5578}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5586 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5586))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5590; FStar_Extraction_ML_Syntax.loc = uu____5591}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5593))) -> begin
(

let uu____5606 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5606))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5610; FStar_Extraction_ML_Syntax.loc = uu____5611}, uu____5612); FStar_Extraction_ML_Syntax.mlty = uu____5613; FStar_Extraction_ML_Syntax.loc = uu____5614}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5626 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5626))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5630; FStar_Extraction_ML_Syntax.loc = uu____5631}, uu____5632); FStar_Extraction_ML_Syntax.mlty = uu____5633; FStar_Extraction_ML_Syntax.loc = uu____5634}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5636))) -> begin
(

let uu____5653 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5653))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5659 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5659))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5663))) -> begin
(

let uu____5672 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5672))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5676; FStar_Extraction_ML_Syntax.loc = uu____5677}, uu____5678), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5685 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5685))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5689; FStar_Extraction_ML_Syntax.loc = uu____5690}, uu____5691), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5692))) -> begin
(

let uu____5705 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5705))
end
| uu____5708 -> begin
mlAppExpr
end)))))


let maybe_promote_effect : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag) = (fun ml_e tag t -> (match (((tag), (t))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| uu____5738 -> begin
((ml_e), (tag))
end))


let extract_lb_sig : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.letbindings  ->  (FStar_Syntax_Syntax.lbname * FStar_Extraction_ML_Syntax.e_tag * (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.binders * FStar_Extraction_ML_Syntax.mltyscheme)) * Prims.bool * FStar_Syntax_Syntax.term) Prims.list = (fun g lbs -> (

let maybe_generalize = (fun uu____5796 -> (match (uu____5796) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____5816; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu____5820; FStar_Syntax_Syntax.lbpos = uu____5821} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let lbtyp1 = (FStar_Syntax_Subst.compress lbtyp)
in (

let no_gen = (fun uu____5899 -> (

let expected_t = (term_as_mlty g lbtyp1)
in ((lbname_), (f_e), (((lbtyp1), ((([]), ((([]), (expected_t))))))), (false), (lbdef))))
in (

let uu____5969 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv lbtyp1)
in (match (uu____5969) with
| true -> begin
((lbname_), (f_e), (((lbtyp1), ((([]), ((([]), (FStar_Extraction_ML_Syntax.MLTY_Erased))))))), (false), (lbdef))
end
| uu____6006 -> begin
(match (lbtyp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____6047 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____6047 (is_type_binder g))) -> begin
(

let uu____6068 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6068) with
| (bs1, c1) -> begin
(

let uu____6093 = (

let uu____6106 = (FStar_Util.prefix_until (fun x -> (

let uu____6152 = (is_type_binder g x)
in (not (uu____6152)))) bs1)
in (match (uu____6106) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____6278 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____6278)))
end))
in (match (uu____6093) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let lbdef1 = (

let uu____6339 = (normalize_abs lbdef)
in (FStar_All.pipe_right uu____6339 FStar_Syntax_Util.unmeta))
in (match (lbdef1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____6387 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____6387) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____6442 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____6442) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____6548 uu____6549 -> (match (((uu____6548), (uu____6549))) with
| ((x, uu____6575), (y, uu____6577)) -> begin
(

let uu____6598 = (

let uu____6605 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____6605)))
in FStar_Syntax_Syntax.NT (uu____6598))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____6622 -> (match (uu____6622) with
| (a, uu____6630) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____6641 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____6659 -> (match (uu____6659) with
| (x, uu____6667) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____6641), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
((

let uu____6681 = (is_fstar_value body1)
in (not (uu____6681))) || (

let uu____6683 = (FStar_Syntax_Util.is_pure_comp c1)
in (not (uu____6683))))
end
| uu____6684 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____6700 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____6702 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((lbtyp1), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____6718 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____6737) -> begin
(

let env = (FStar_List.fold_left (fun env uu____6756 -> (match (uu____6756) with
| (a, uu____6764) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____6775 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____6793 -> (match (uu____6793) with
| (x, uu____6801) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____6775), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____6845 -> (match (uu____6845) with
| (bv, uu____6853) -> begin
(

let uu____6858 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____6858 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6886) -> begin
(

let env = (FStar_List.fold_left (fun env uu____6899 -> (match (uu____6899) with
| (a, uu____6907) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____6918 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____6936 -> (match (uu____6936) with
| (x, uu____6944) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____6918), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____6988 -> (match (uu____6988) with
| (bv, uu____6996) -> begin
(

let uu____7001 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____7001 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____7029) -> begin
(

let env = (FStar_List.fold_left (fun env uu____7042 -> (match (uu____7042) with
| (a, uu____7050) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____7061 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____7079 -> (match (uu____7079) with
| (x, uu____7087) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____7061), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____7131 -> (match (uu____7131) with
| (bv, uu____7139) -> begin
(

let uu____7144 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____7144 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| uu____7172 -> begin
(err_value_restriction lbdef1)
end)))
end))
end))
end
| uu____7191 -> begin
(no_gen ())
end)
end)))))
end))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map maybe_generalize))))


let extract_lb_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.letbindings  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list) = (fun g lbs -> (

let is_top = (FStar_Syntax_Syntax.is_top_level (FStar_Pervasives_Native.snd lbs))
in (

let is_rec = ((not (is_top)) && (FStar_Pervasives_Native.fst lbs))
in (

let lbs1 = (extract_lb_sig g lbs)
in (FStar_Util.fold_map (fun env uu____7332 -> (match (uu____7332) with
| (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body) -> begin
(

let uu____7390 = (FStar_Extraction_ML_UEnv.extend_lb env lbname typ mltyscheme add_unit is_rec)
in (match (uu____7390) with
| (env1, uu____7406, exp_binding) -> begin
(

let uu____7408 = (

let uu____7413 = (FStar_Util.right lbname)
in ((uu____7413), (exp_binding)))
in ((env1), (uu____7408)))
end))
end)) g lbs1)))))


let rec check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e f ty -> ((FStar_Extraction_ML_UEnv.debug g (fun uu____7478 -> (

let uu____7479 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____7480 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.print2 "Checking %s at type %s\n" uu____7479 uu____7480)))));
(match (((f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____7485) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____7486 -> begin
(

let uu____7491 = (term_as_mlexpr g e)
in (match (uu____7491) with
| (ml_e, tag, t) -> begin
(

let uu____7505 = (maybe_promote_effect ml_e tag t)
in (match (uu____7505) with
| (ml_e1, tag1) -> begin
(

let uu____7516 = (FStar_Extraction_ML_Util.eff_leq tag1 f)
in (match (uu____7516) with
| true -> begin
(

let uu____7521 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____7521), (ty)))
end
| uu____7522 -> begin
(match (((tag1), (f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(

let uu____7527 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____7527), (ty)))
end
| uu____7528 -> begin
((err_unexpected_eff g e ty f tag1);
(

let uu____7536 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____7536), (ty)));
)
end)
end))
end))
end))
end);
))
and term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let uu____7539 = (term_as_mlexpr' g e)
in (match (uu____7539) with
| (e1, f, t) -> begin
(

let uu____7555 = (maybe_promote_effect e1 f t)
in (match (uu____7555) with
| (e2, f1) -> begin
((e2), (f1), (t))
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____7580 = (

let uu____7581 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____7582 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____7583 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____7581 uu____7582 uu____7583))))
in (FStar_Util.print_string uu____7580))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____7591 = (

let uu____7592 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____7592))
in (failwith uu____7591))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____7599) -> begin
(

let uu____7622 = (

let uu____7623 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____7623))
in (failwith uu____7622))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____7630) -> begin
(

let uu____7643 = (

let uu____7644 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____7644))
in (failwith uu____7643))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____7651) -> begin
(

let uu____7652 = (

let uu____7653 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____7653))
in (failwith uu____7652))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____7661 = (FStar_Syntax_Util.unfold_lazy i)
in (term_as_mlexpr g uu____7661))
end
| FStar_Syntax_Syntax.Tm_type (uu____7662) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____7663) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7670) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____7686}) -> begin
(

let uu____7699 = (

let uu____7700 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____7700))
in (match (uu____7699) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____7707; FStar_Extraction_ML_UEnv.exp_b_expr = fw; FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____7709; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____7710} -> begin
(

let uu____7711 = (

let uu____7712 = (

let uu____7713 = (

let uu____7720 = (

let uu____7723 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Cannot evaluate open quotation at runtime"))))
in (uu____7723)::[])
in ((fw), (uu____7720)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____7713))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____7712))
in ((uu____7711), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) -> begin
(

let uu____7740 = (FStar_Reflection_Basic.inspect_ln qt)
in (match (uu____7740) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____7748 = (FStar_Syntax_Syntax.lookup_aq bv aqs)
in (match (uu____7748) with
| FStar_Pervasives_Native.Some (tm) -> begin
(term_as_mlexpr g tm)
end
| FStar_Pervasives_Native.None -> begin
(

let tv = (

let uu____7759 = (

let uu____7766 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____7766 (FStar_Reflection_Data.Tv_Var (bv))))
in (uu____7759 t.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in (

let t1 = (

let uu____7797 = (

let uu____7808 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____7808)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____7797))
in (term_as_mlexpr g t1)))
end))
end
| tv -> begin
(

let tv1 = (

let uu____7835 = (

let uu____7842 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____7842 tv))
in (uu____7835 t.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in (

let t1 = (

let uu____7873 = (

let uu____7884 = (FStar_Syntax_Syntax.as_arg tv1)
in (uu____7884)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____7873))
in (term_as_mlexpr g t1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____7911)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____7941 = (

let uu____7948 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____7948))
in (match (uu____7941) with
| (ed, qualifiers) -> begin
(

let uu____7975 = (

let uu____7976 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.tcenv ed.FStar_Syntax_Syntax.mname)
in (not (uu____7976)))
in (match (uu____7975) with
| true -> begin
(term_as_mlexpr g t2)
end
| uu____7983 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____7990 -> begin
(term_as_mlexpr g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____7992) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____7998) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____8004 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____8004) with
| (uu____8017, ty, uu____8019) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____8021 = (

let uu____8022 = (FStar_Extraction_ML_Util.mlexpr_of_const t.FStar_Syntax_Syntax.pos c)
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____8022))
in ((uu____8021), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____8023) -> begin
(

let uu____8024 = (is_type g t)
in (match (uu____8024) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____8031 -> begin
(

let uu____8032 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____8032) with
| (FStar_Util.Inl (uu____8045), uu____8046) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr ({FStar_Extraction_ML_UEnv.exp_b_name = uu____8051; FStar_Extraction_ML_UEnv.exp_b_expr = x; FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____8054}), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____8068 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____8068), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____8069 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8077 = (is_type g t)
in (match (uu____8077) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____8084 -> begin
(

let uu____8085 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____8085) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_UEnv.exp_b_name = uu____8094; FStar_Extraction_ML_UEnv.exp_b_expr = x; FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____8097}) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____8106 = (maybe_eta_data_and_project_record g fv.FStar_Syntax_Syntax.fv_qual t1 x)
in ((uu____8106), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____8107 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, rcopt) -> begin
(

let uu____8141 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____8141) with
| (bs1, body1) -> begin
(

let uu____8154 = (binders_as_ml_binders g bs1)
in (match (uu____8154) with
| (ml_bs, env) -> begin
(

let body2 = (match (rcopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8187 = (FStar_TypeChecker_Env.is_reifiable_rc env.FStar_Extraction_ML_UEnv.tcenv rc)
in (match (uu____8187) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____8188 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____8192 -> (

let uu____8193 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____8193))));
body1;
)
end)
in (

let uu____8194 = (term_as_mlexpr env body2)
in (match (uu____8194) with
| (ml_body, f, t1) -> begin
(

let uu____8210 = (FStar_List.fold_right (fun uu____8229 uu____8230 -> (match (((uu____8229), (uu____8230))) with
| ((uu____8251, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____8210) with
| (f1, tfun) -> begin
(

let uu____8271 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____8271), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____8278; FStar_Syntax_Syntax.vars = uu____8279}, ((a1, uu____8281))::[]) -> begin
(

let ty = (

let uu____8321 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (term_as_mlty g uu____8321))
in (

let uu____8322 = (

let uu____8323 = (FStar_Extraction_ML_Util.mlexpr_of_range a1.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) uu____8323))
in ((uu____8322), (FStar_Extraction_ML_Syntax.E_PURE), (ty))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____8324; FStar_Syntax_Syntax.vars = uu____8325}, ((t1, uu____8327))::((r, uu____8329))::[]) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____8384)); FStar_Syntax_Syntax.pos = uu____8385; FStar_Syntax_Syntax.vars = uu____8386}, uu____8387) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___366_8453 -> (match (uu___366_8453) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____8454 -> begin
false
end))))))
in (

let uu____8455 = (

let uu____8460 = (

let uu____8461 = (FStar_Syntax_Subst.compress head1)
in uu____8461.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____8460)))
in (match (uu____8455) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____8470), uu____8471) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____8485, FStar_Syntax_Syntax.Tm_abs (bs, uu____8487, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____8512, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____8514 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____8514))
in (

let tm = (

let uu____8526 = (

let uu____8531 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____8532 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____8531 uu____8532)))
in (uu____8526 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr g tm)))
end
| uu____8543 -> begin
(

let rec extract_app = (fun is_data uu____8596 uu____8597 restArgs -> (match (((uu____8596), (uu____8597))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(

let mk_head = (fun uu____8678 -> (

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (

let head2 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (maybe_coerce top.FStar_Syntax_Syntax.pos g head2 FStar_Extraction_ML_Syntax.MLTY_Top t1))))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____8706 -> (

let uu____8707 = (

let uu____8708 = (mk_head ())
in (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule uu____8708))
in (

let uu____8709 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t1)
in (

let uu____8710 = (match (restArgs) with
| [] -> begin
"none"
end
| ((hd1, uu____8718))::uu____8719 -> begin
(FStar_Syntax_Print.term_to_string hd1)
end)
in (FStar_Util.print3 "extract_app ml_head=%s type of head = %s, next arg = %s\n" uu____8707 uu____8709 uu____8710))))));
(match (((restArgs), (t1))) with
| ([], uu____8752) -> begin
(

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (

let app = (

let uu____8787 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____8787))
in ((app), (f), (t1))))
end
| (((arg, uu____8791))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____8822 = (

let uu____8827 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____8827), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____8822 rest))
end
| (((e0, uu____8839))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let expected_effect = (

let uu____8872 = ((FStar_Options.lax ()) && (FStar_TypeChecker_Util.short_circuit_head head1))
in (match (uu____8872) with
| true -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| uu____8873 -> begin
FStar_Extraction_ML_Syntax.E_PURE
end))
in (

let uu____8874 = (check_term_as_mlexpr g e0 expected_effect tExpected)
in (match (uu____8874) with
| (e01, tInferred) -> begin
(

let uu____8887 = (

let uu____8892 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::[]))
in ((uu____8892), (t2)))
in (extract_app is_data ((mlhead), ((((e01), (expected_effect)))::mlargs_f)) uu____8887 rest))
end))))
end
| uu____8903 -> begin
(

let uu____8916 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____8916) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(match (t1) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let t2 = (FStar_List.fold_right (fun t2 out -> FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.E_PURE), (out)))) restArgs FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let mlhead1 = (

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (

let head2 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (maybe_coerce top.FStar_Syntax_Syntax.pos g head2 FStar_Extraction_ML_Syntax.MLTY_Top t2)))
in (extract_app is_data ((mlhead1), ([])) ((f), (t2)) restArgs)))
end
| uu____8988 -> begin
(

let mlhead1 = (

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (

let head2 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (maybe_coerce top.FStar_Syntax_Syntax.pos g head2 FStar_Extraction_ML_Syntax.MLTY_Top t1)))
in (err_ill_typed_application g top mlhead1 restArgs t1))
end)
end))
end);
))
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____9059 args1 -> (match (uu____9059) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____9089)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9173))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____9175, f', t3)) -> begin
(

let uu____9212 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____9212 t3))
end
| uu____9213 -> begin
((args2), (f1), (t2))
end))
in (

let uu____9238 = (remove_implicits args1 f t1)
in (match (uu____9238) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____9294 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let extract_app_with_instantiations = (fun uu____9318 -> (

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (uu____9326) -> begin
(

let uu____9327 = (

let uu____9346 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____9346) with
| (FStar_Util.Inr (exp_b), q) -> begin
((((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr), (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme), (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok))), (q))
end
| uu____9397 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____9327) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____9461))::uu____9462 -> begin
(is_type g a)
end
| uu____9489 -> begin
false
end)
in (

let uu____9500 = (match (vars) with
| (uu____9529)::uu____9530 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____9541 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____9573 = (FStar_Util.first_N n1 args)
in (match (uu____9573) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____9678 -> (match (uu____9678) with
| (x, uu____9686) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____9707 -> begin
(

let uu___372_9710 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___372_9710.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___372_9710.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____9714) -> begin
(

let uu___373_9715 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___373_9715.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___373_9715.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____9716) -> begin
(

let uu___373_9717 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___373_9717.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___373_9717.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____9719; FStar_Extraction_ML_Syntax.loc = uu____9720})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___374_9726 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___374_9726.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___374_9726.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____9727 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____9736 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____9500) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____9790 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____9790), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____9791 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____9800) -> begin
(

let uu____9801 = (

let uu____9820 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____9820) with
| (FStar_Util.Inr (exp_b), q) -> begin
((((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr), (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme), (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok))), (q))
end
| uu____9871 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____9801) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____9935))::uu____9936 -> begin
(is_type g a)
end
| uu____9963 -> begin
false
end)
in (

let uu____9974 = (match (vars) with
| (uu____10003)::uu____10004 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____10015 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____10047 = (FStar_Util.first_N n1 args)
in (match (uu____10047) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____10152 -> (match (uu____10152) with
| (x, uu____10160) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____10181 -> begin
(

let uu___372_10184 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___372_10184.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___372_10184.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____10188) -> begin
(

let uu___373_10189 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___373_10189.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___373_10189.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____10190) -> begin
(

let uu___373_10191 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___373_10191.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___373_10191.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____10193; FStar_Extraction_ML_Syntax.loc = uu____10194})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___374_10200 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___374_10200.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___374_10200.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____10201 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____10210 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____9974) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____10264 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____10264), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____10265 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____10274 -> begin
(

let uu____10275 = (term_as_mlexpr g head2)
in (match (uu____10275) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end)))
in (

let uu____10291 = (is_type g t)
in (match (uu____10291) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____10298 -> begin
(

let uu____10299 = (

let uu____10300 = (FStar_Syntax_Util.un_uinst head1)
in uu____10300.FStar_Syntax_Syntax.n)
in (match (uu____10299) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____10310 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____10310) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____10319 -> begin
(extract_app_with_instantiations ())
end))
end
| uu____10322 -> begin
(extract_app_with_instantiations ())
end))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____10325), f) -> begin
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

let uu____10392 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____10392) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____10423 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____10436 -> begin
(

let uu____10437 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____10437) with
| true -> begin
((lbs), (e'))
end
| uu____10446 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____10449 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____10449))
in (

let lb1 = (

let uu___375_10451 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___375_10451.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___375_10451.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___375_10451.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___375_10451.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___375_10451.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___375_10451.FStar_Syntax_Syntax.lbpos})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____10423) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____10482 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____10482))
in (

let lbdef = (

let uu____10490 = (FStar_Options.ml_ish ())
in (match (uu____10490) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____10493 -> begin
(

let norm_call = (fun uu____10499 -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.PureSubtermsWithinComputations)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.ForExtraction)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef))
in (

let uu____10500 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("Extraction"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("ExtractNorm"))))
in (match (uu____10500) with
| true -> begin
(

let a = (

let uu____10506 = (

let uu____10507 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.format1 "(Time to normalize top-level let %s)" uu____10507))
in (FStar_Util.measure_execution_time uu____10506 norm_call))
in ((

let uu____10511 = (FStar_Syntax_Print.term_to_string a)
in (FStar_Util.print1 "Normalized to %s\n" uu____10511));
a;
))
end
| uu____10512 -> begin
(norm_call ())
end)))
end))
in (

let uu___376_10513 = lb
in {FStar_Syntax_Syntax.lbname = uu___376_10513.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___376_10513.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___376_10513.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___376_10513.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___376_10513.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___376_10513.FStar_Syntax_Syntax.lbpos}))))))
end
| uu____10514 -> begin
lbs1
end)
in (

let check_lb = (fun env uu____10563 -> (match (uu____10563) with
| (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____10712 -> (match (uu____10712) with
| (a, uu____10720) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____10726 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____10726) with
| (e1, ty) -> begin
(

let uu____10737 = (maybe_promote_effect e1 f expected_t)
in (match (uu____10737) with
| (e2, f1) -> begin
(

let meta = (match (((f1), (ty))) with
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| uu____10749 -> begin
[]
end)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e2; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = true})))
end))
end))))
end))
in (

let lbs3 = (extract_lb_sig g ((is_rec), (lbs2)))
in (

let uu____10777 = (FStar_List.fold_right (fun lb uu____10869 -> (match (uu____10869) with
| (env, lbs4) -> begin
(

let uu____10994 = lb
in (match (uu____10994) with
| (lbname, uu____11042, (t1, (uu____11044, polytype)), add_unit, uu____11047) -> begin
(

let uu____11060 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____11060) with
| (env1, nm, uu____11097) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____10777) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____11265 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____11354 = (term_as_mlexpr env_body e'1)
in (match (uu____11354) with
| (e'2, f', t') -> begin
(

let f = (

let uu____11371 = (

let uu____11374 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____11374)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____11371))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____11382 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____11383 = (

let uu____11384 = (

let uu____11385 = (

let uu____11386 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), (uu____11386)))
in (mk_MLE_Let top_level uu____11385 e'2))
in (

let uu____11395 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____11384 uu____11395)))
in ((uu____11383), (f), (t')))))
end)))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____11434 = (term_as_mlexpr g scrutinee)
in (match (uu____11434) with
| (e, f_e, t_e) -> begin
(

let uu____11450 = (check_pats_for_ite pats)
in (match (uu____11450) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____11511 = (term_as_mlexpr g then_e1)
in (match (uu____11511) with
| (then_mle, f_then, t_then) -> begin
(

let uu____11527 = (term_as_mlexpr g else_e1)
in (match (uu____11527) with
| (else_mle, f_else, t_else) -> begin
(

let uu____11543 = (

let uu____11554 = (type_leq g t_then t_else)
in (match (uu____11554) with
| true -> begin
((t_else), (no_lift))
end
| uu____11571 -> begin
(

let uu____11572 = (type_leq g t_else t_then)
in (match (uu____11572) with
| true -> begin
((t_then), (no_lift))
end
| uu____11589 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____11543) with
| (t_branch, maybe_lift1) -> begin
(

let uu____11616 = (

let uu____11617 = (

let uu____11618 = (

let uu____11627 = (maybe_lift1 then_mle t_then)
in (

let uu____11628 = (

let uu____11631 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____11631))
in ((e), (uu____11627), (uu____11628))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____11618))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____11617))
in (

let uu____11634 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____11616), (uu____11634), (t_branch))))
end))
end))
end))
end
| uu____11635 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____11650 -> begin
(

let uu____11651 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____11746 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____11746) with
| (pat, when_opt, branch1) -> begin
(

let uu____11790 = (extract_pat g pat t_e term_as_mlexpr)
in (match (uu____11790) with
| (env, p, pat_t_compat) -> begin
(

let uu____11848 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let w_pos = w.FStar_Syntax_Syntax.pos
in (

let uu____11871 = (term_as_mlexpr env w)
in (match (uu____11871) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce w_pos env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end)))
end)
in (match (uu____11848) with
| (when_opt1, f_when) -> begin
(

let uu____11920 = (term_as_mlexpr env branch1)
in (match (uu____11920) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____11954 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12031 -> (match (uu____12031) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____11954)))
end))
end))
end))
end))) true))
in (match (uu____11651) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____12191 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____12196 -> (

let uu____12197 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____12198 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____12197 uu____12198)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____12223 = (

let uu____12224 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____12224))
in (match (uu____12223) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____12231; FStar_Extraction_ML_UEnv.exp_b_expr = fw; FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____12233; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____12234} -> begin
(

let uu____12235 = (

let uu____12236 = (

let uu____12237 = (

let uu____12244 = (

let uu____12247 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____12247)::[])
in ((fw), (uu____12244)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____12237))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____12236))
in ((uu____12235), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| ((uu____12250, uu____12251, (uu____12252, f_first, t_first)))::rest -> begin
(

let uu____12312 = (FStar_List.fold_left (fun uu____12354 uu____12355 -> (match (((uu____12354), (uu____12355))) with
| ((topt, f), (uu____12412, uu____12413, (uu____12414, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____12470 = (type_leq g t1 t_branch)
in (match (uu____12470) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____12473 -> begin
(

let uu____12474 = (type_leq g t_branch t1)
in (match (uu____12474) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____12477 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____12312) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____12569 -> (match (uu____12569) with
| (p, (wopt, uu____12598), (b1, uu____12600, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____12619) -> begin
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

let uu____12624 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____12624), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____12650 = (

let uu____12655 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12655))
in (match (uu____12650) with
| (uu____12680, fstar_disc_type) -> begin
(

let wildcards = (

let uu____12689 = (

let uu____12690 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____12690.FStar_Syntax_Syntax.n)
in (match (uu____12689) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____12700) -> begin
(

let uu____12721 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___367_12755 -> (match (uu___367_12755) with
| (uu____12762, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12763))) -> begin
true
end
| uu____12766 -> begin
false
end))))
in (FStar_All.pipe_right uu____12721 (FStar_List.map (fun uu____12799 -> (

let uu____12806 = (fresh "_")
in ((uu____12806), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____12807 -> begin
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

let uu____12818 = (

let uu____12819 = (

let uu____12830 = (

let uu____12831 = (

let uu____12832 = (

let uu____12847 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____12850 = (

let uu____12861 = (

let uu____12870 = (

let uu____12871 = (

let uu____12878 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____12878), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____12871))
in (

let uu____12881 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____12870), (FStar_Pervasives_Native.None), (uu____12881))))
in (

let uu____12884 = (

let uu____12895 = (

let uu____12904 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____12904)))
in (uu____12895)::[])
in (uu____12861)::uu____12884))
in ((uu____12847), (uu____12850))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____12832))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____12831))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____12830)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____12819))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____12818))
in (

let uu____12959 = (

let uu____12960 = (

let uu____12963 = (

let uu____12964 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____12964; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____12963)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), (uu____12960)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____12959)))))))
end)))




