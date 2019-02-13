
open Prims
open FStar_Pervasives
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____9 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields : 'Auu____78 . FStar_Ident.ident Prims.list  ->  'Auu____78 Prims.list  ->  (Prims.string * 'Auu____78) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail : 'Auu____121 . FStar_Range.range  ->  (FStar_Errors.raw_error * Prims.string)  ->  'Auu____121 = (fun r err -> (FStar_Errors.raise_error err r))


let err_uninst : 'Auu____153 . FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Syntax_Syntax.term  ->  'Auu____153 = (fun env t uu____179 app -> (match (uu____179) with
| (vars, ty) -> begin
(

let uu____196 = (

let uu____202 = (

let uu____204 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____206 = (FStar_All.pipe_right vars (FStar_String.concat ", "))
in (

let uu____213 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____215 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____204 uu____206 uu____213 uu____215)))))
in ((FStar_Errors.Fatal_Uninstantiated), (uu____202)))
in (fail t.FStar_Syntax_Syntax.pos uu____196))
end))


let err_ill_typed_application : 'Auu____234 'Auu____235 . FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  (FStar_Syntax_Syntax.term * 'Auu____234) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____235 = (fun env t mlhead args ty -> (

let uu____273 = (

let uu____279 = (

let uu____281 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____283 = (FStar_Extraction_ML_Code.string_of_mlexpr env.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (

let uu____285 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____287 = (

let uu____289 = (FStar_All.pipe_right args (FStar_List.map (fun uu____310 -> (match (uu____310) with
| (x, uu____317) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____289 (FStar_String.concat " ")))
in (FStar_Util.format4 "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n" uu____281 uu____283 uu____285 uu____287)))))
in ((FStar_Errors.Fatal_IllTyped), (uu____279)))
in (fail t.FStar_Syntax_Syntax.pos uu____273)))


let err_ill_typed_erasure : 'Auu____334 . FStar_Extraction_ML_UEnv.uenv  ->  FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____334 = (fun env pos ty -> (

let uu____350 = (

let uu____356 = (

let uu____358 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format1 "Erased value found where a value of type %s was expected" uu____358))
in ((FStar_Errors.Fatal_IllTyped), (uu____356)))
in (fail pos uu____350)))


let err_value_restriction : 'Auu____367 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____367 = (fun t -> (

let uu____377 = (

let uu____383 = (

let uu____385 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____387 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____385 uu____387)))
in ((FStar_Errors.Fatal_ValueRestriction), (uu____383)))
in (fail t.FStar_Syntax_Syntax.pos uu____377)))


let err_unexpected_eff : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  unit = (fun env t ty f0 f1 -> (

let uu____421 = (

let uu____427 = (

let uu____429 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____431 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____433 = (FStar_Extraction_ML_Util.eff_to_string f0)
in (

let uu____435 = (FStar_Extraction_ML_Util.eff_to_string f1)
in (FStar_Util.format4 "for expression %s of type %s, Expected effect %s; got effect %s" uu____429 uu____431 uu____433 uu____435)))))
in ((FStar_Errors.Warning_ExtractionUnexpectedEffect), (uu____427)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____421)))


let effect_as_etag : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____463 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____463) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____468 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.env_tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____468) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____479, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (

let uu____489 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)
in (match (uu____489) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____492 -> begin
(

let uu____494 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____494) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____497 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.env_tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____520 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____520) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____523 -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end
| FStar_Pervasives_Native.None -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end))
end))))))


let rec is_arity : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let uu____544 = (

let uu____545 = (FStar_Syntax_Subst.compress t1)
in uu____545.FStar_Syntax_Syntax.n)
in (match (uu____544) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____551) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____576) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____605) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____615 = (FStar_Syntax_Util.unfold_lazy i)
in (is_arity env uu____615))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____616) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____630) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____632) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____634) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____642) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____644) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____646, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____668) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env.FStar_Extraction_ML_UEnv.env_tcenv t1)
in (

let uu____670 = (

let uu____671 = (FStar_Syntax_Subst.compress t2)
in uu____671.FStar_Syntax_Syntax.n)
in (match (uu____670) with
| FStar_Syntax_Syntax.Tm_fvar (uu____675) -> begin
false
end
| uu____677 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____678) -> begin
(

let uu____695 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____695) with
| (head1, uu____714) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____740) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____746) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____751, body, uu____753) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____778, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____798, branches) -> begin
(match (branches) with
| ((uu____837, uu____838, e))::uu____840 -> begin
(is_arity env e)
end
| uu____887 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____919) -> begin
(

let uu____942 = (

let uu____944 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____944))
in (failwith uu____942))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____948 = (

let uu____950 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____950))
in (failwith uu____948))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____955 = (FStar_Syntax_Util.unfold_lazy i)
in (is_type_aux env uu____955))
end
| FStar_Syntax_Syntax.Tm_constant (uu____956) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____958) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____960) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____968) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uu____987; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____988; FStar_Syntax_Syntax.ctx_uvar_binders = uu____989; FStar_Syntax_Syntax.ctx_uvar_typ = t2; FStar_Syntax_Syntax.ctx_uvar_reason = uu____991; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____992; FStar_Syntax_Syntax.ctx_uvar_range = uu____993; FStar_Syntax_Syntax.ctx_uvar_meta = uu____994}, s) -> begin
(

let uu____1043 = (FStar_Syntax_Subst.subst' s t2)
in (is_arity env uu____1043))
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____1044; FStar_Syntax_Syntax.index = uu____1045; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____1050; FStar_Syntax_Syntax.index = uu____1051; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1057, uu____1058) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1100) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1107) -> begin
(

let uu____1132 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____1132) with
| (uu____1138, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1158 = (

let uu____1163 = (

let uu____1164 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1164)::[])
in (FStar_Syntax_Subst.open_term uu____1163 body))
in (match (uu____1158) with
| (uu____1184, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1186, lbs), body) -> begin
(

let uu____1206 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____1206) with
| (uu____1214, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____1220, branches) -> begin
(match (branches) with
| (b)::uu____1260 -> begin
(

let uu____1305 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____1305) with
| (uu____1307, uu____1308, e) -> begin
(is_type_aux env e)
end))
end
| uu____1326 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1344) -> begin
false
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1353) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1359) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1400 -> (

let uu____1401 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1403 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1401 uu____1403)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1412 -> (match (b) with
| true -> begin
(

let uu____1414 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1416 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1414 uu____1416)))
end
| uu____1419 -> begin
(

let uu____1421 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1423 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1421 uu____1423)))
end)));
b;
));
))


let is_type_binder : 'Auu____1433 . FStar_Extraction_ML_UEnv.uenv  ->  (FStar_Syntax_Syntax.bv * 'Auu____1433)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1460 = (

let uu____1461 = (FStar_Syntax_Subst.compress t)
in uu____1461.FStar_Syntax_Syntax.n)
in (match (uu____1460) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1465; FStar_Syntax_Syntax.fv_delta = uu____1466; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1468; FStar_Syntax_Syntax.fv_delta = uu____1469; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1470))}) -> begin
true
end
| uu____1478 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1487 = (

let uu____1488 = (FStar_Syntax_Subst.compress t)
in uu____1488.FStar_Syntax_Syntax.n)
in (match (uu____1487) with
| FStar_Syntax_Syntax.Tm_constant (uu____1492) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1494) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1496) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1498) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1544 = (is_constructor head1)
in (match (uu____1544) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1566 -> (match (uu____1566) with
| (te, uu____1575) -> begin
(is_fstar_value te)
end))))
end
| uu____1580 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1584) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1590, uu____1591) -> begin
(is_fstar_value t1)
end
| uu____1632 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1642) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1644) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1647) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1649) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1662, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1671, fields) -> begin
(FStar_Util.for_all (fun uu____1701 -> (match (uu____1701) with
| (uu____1708, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1713) -> begin
(is_ml_value h)
end
| uu____1718 -> begin
false
end))


let fresh : Prims.string  ->  Prims.string = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1769 = (

let uu____1771 = (FStar_ST.op_Bang c)
in (FStar_Util.string_of_int uu____1771))
in (Prims.strcat x uu____1769));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1896 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1898 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1898) with
| true -> begin
(aux bs e' copt)
end
| uu____1903 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1912 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1912))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____2001 -> begin
(

let uu____2003 = (FStar_List.hd l)
in (match (uu____2003) with
| (p1, w1, e1) -> begin
(

let uu____2038 = (

let uu____2047 = (FStar_List.tl l)
in (FStar_List.hd uu____2047))
in (match (uu____2038) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____2131 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____2170 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____2170) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____2186 -> begin
(

let vs = (FStar_List.map (fun uu____2194 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____2208 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____2225 -> (match (uu____2225) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____2208))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let default_value_for_ty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g t -> (

let uu____2256 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____2256) with
| (ts, r) -> begin
(

let body = (fun r1 -> (

let r2 = (

let uu____2276 = (FStar_Extraction_ML_Util.udelta_unfold g r1)
in (match (uu____2276) with
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
| uu____2280 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased), (r2)))))
end)))
in (match ((Prims.op_Equality ts [])) with
| true -> begin
(body r)
end
| uu____2284 -> begin
(

let vs = (FStar_List.map (fun uu____2292 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let uu____2303 = (

let uu____2304 = (

let uu____2316 = (body r)
in ((vs_ts), (uu____2316)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____2304))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) uu____2303))))
end))
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____2335 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____2338 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____2338 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))))
in (match (uu____2335) with
| true -> begin
e
end
| uu____2344 -> begin
(eta_expand expect e)
end)))


let apply_coercion : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let mk_fun = (fun binder body -> (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (binders, body1) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((binder)::binders), (body1)))
end
| uu____2416 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((binder)::[]), (body)))
end))
in (

let rec aux = (fun e1 ty1 expect1 -> (

let coerce_branch = (fun uu____2471 -> (match (uu____2471) with
| (pat, w, b) -> begin
(

let uu____2495 = (aux b ty1 expect1)
in ((pat), (w), (uu____2495)))
end))
in (match (((e1.FStar_Extraction_ML_Syntax.expr), (ty1), (expect1))) with
| (FStar_Extraction_ML_Syntax.MLE_Fun ((arg)::rest, body), FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2502, t1), FStar_Extraction_ML_Syntax.MLTY_Fun (s0, uu____2505, s1)) -> begin
(

let body1 = (match (rest) with
| [] -> begin
body
end
| uu____2537 -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Fun (((rest), (body)))))
end)
in (

let body2 = (aux body1 t1 s1)
in (

let uu____2553 = (type_leq g s0 t0)
in (match (uu____2553) with
| true -> begin
(FStar_Extraction_ML_Syntax.with_ty expect1 (mk_fun arg body2))
end
| uu____2556 -> begin
(

let lb = (

let uu____2559 = (

let uu____2560 = (

let uu____2561 = (

let uu____2568 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty s0) (FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Pervasives_Native.fst arg))))
in ((uu____2568), (s0), (t0)))
in FStar_Extraction_ML_Syntax.MLE_Coerce (uu____2561))
in (FStar_Extraction_ML_Syntax.with_ty t0 uu____2560))
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.fst arg); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (t0))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = uu____2559; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (

let body3 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty s1) (FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))), (body2)))))
in (FStar_Extraction_ML_Syntax.with_ty expect1 (mk_fun (((FStar_Pervasives_Native.fst arg)), (s0)) body3))))
end))))
end
| (FStar_Extraction_ML_Syntax.MLE_Let (lbs, body), uu____2587, uu____2588) -> begin
(

let uu____2601 = (

let uu____2602 = (

let uu____2613 = (aux body ty1 expect1)
in ((lbs), (uu____2613)))
in FStar_Extraction_ML_Syntax.MLE_Let (uu____2602))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2601))
end
| (FStar_Extraction_ML_Syntax.MLE_Match (s, branches), uu____2622, uu____2623) -> begin
(

let uu____2644 = (

let uu____2645 = (

let uu____2660 = (FStar_List.map coerce_branch branches)
in ((s), (uu____2660)))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____2645))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2644))
end
| (FStar_Extraction_ML_Syntax.MLE_If (s, b1, b2_opt), uu____2700, uu____2701) -> begin
(

let uu____2706 = (

let uu____2707 = (

let uu____2716 = (aux b1 ty1 expect1)
in (

let uu____2717 = (FStar_Util.map_opt b2_opt (fun b2 -> (aux b2 ty1 expect1)))
in ((s), (uu____2716), (uu____2717))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____2707))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2706))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es), uu____2725, uu____2726) -> begin
(

let uu____2729 = (FStar_Util.prefix es)
in (match (uu____2729) with
| (prefix1, last1) -> begin
(

let uu____2742 = (

let uu____2743 = (

let uu____2746 = (

let uu____2749 = (aux last1 ty1 expect1)
in (uu____2749)::[])
in (FStar_List.append prefix1 uu____2746))
in FStar_Extraction_ML_Syntax.MLE_Seq (uu____2743))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2742))
end))
end
| (FStar_Extraction_ML_Syntax.MLE_Try (s, branches), uu____2752, uu____2753) -> begin
(

let uu____2774 = (

let uu____2775 = (

let uu____2790 = (FStar_List.map coerce_branch branches)
in ((s), (uu____2790)))
in FStar_Extraction_ML_Syntax.MLE_Try (uu____2775))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2774))
end
| uu____2827 -> begin
(FStar_Extraction_ML_Syntax.with_ty expect1 (FStar_Extraction_ML_Syntax.MLE_Coerce (((e1), (ty1), (expect1)))))
end)))
in (aux e ty expect))))


let maybe_coerce : 'Auu____2847 . 'Auu____2847  ->  FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun pos g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____2874 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____2874) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____2887 -> begin
(match (ty1) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(default_value_for_ty g expect)
end
| uu____2895 -> begin
(

let uu____2896 = (

let uu____2898 = (FStar_Extraction_ML_Util.erase_effect_annotations ty1)
in (

let uu____2899 = (FStar_Extraction_ML_Util.erase_effect_annotations expect)
in (type_leq g uu____2898 uu____2899)))
in (match (uu____2896) with
| true -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2905 -> (

let uu____2906 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____2908 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (FStar_Util.print2 "\n Effect mismatch on type of %s : %s\n" uu____2906 uu____2908)))));
e;
)
end
| uu____2911 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2918 -> (

let uu____2919 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____2921 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____2923 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____2919 uu____2921 uu____2923))))));
(

let uu____2926 = (apply_coercion g e ty1 expect)
in (maybe_eta_expand expect uu____2926));
)
end))
end)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____2938 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____2938) with
| FStar_Util.Inl (ty_b) -> begin
ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
end
| uu____2940 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let basic_norm_steps : FStar_TypeChecker_Env.step Prims.list = (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]


let comp_no_args : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2958) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____2967) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let effect_args = (FStar_List.map (fun uu____3003 -> (match (uu____3003) with
| (uu____3018, aq) -> begin
((FStar_Syntax_Syntax.t_unit), (aq))
end)) ct.FStar_Syntax_Syntax.effect_args)
in (

let ct1 = (

let uu___371_3031 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___371_3031.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___371_3031.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___371_3031.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = uu___371_3031.FStar_Syntax_Syntax.flags})
in (

let c1 = (

let uu___372_3035 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___372_3035.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___372_3035.FStar_Syntax_Syntax.vars})
in c1)))
end))


let rec translate_term_to_mlty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let arg_as_mlty = (fun g1 uu____3084 -> (match (uu____3084) with
| (a, uu____3092) -> begin
(

let uu____3097 = (is_type g1 a)
in (match (uu____3097) with
| true -> begin
(translate_term_to_mlty g1 a)
end
| uu____3100 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
in (

let fv_app_as_mlty = (fun g1 fv args -> (

let uu____3118 = (

let uu____3120 = (FStar_Extraction_ML_UEnv.is_fv_type g1 fv)
in (not (uu____3120)))
in (match (uu____3118) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| uu____3123 -> begin
(

let uu____3125 = (

let uu____3140 = (FStar_TypeChecker_Env.lookup_lid g1.FStar_Extraction_ML_UEnv.env_tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3140) with
| ((uu____3163, fvty), uu____3165) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) g1.FStar_Extraction_ML_UEnv.env_tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____3125) with
| (formals, uu____3172) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g1) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____3229 = (FStar_Util.first_N n_args formals)
in (match (uu____3229) with
| (uu____3262, rest) -> begin
(

let uu____3296 = (FStar_List.map (fun uu____3306 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____3296))
end))
end
| uu____3313 -> begin
mlargs
end))
in (

let nm = (

let uu____3316 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv)
in (match (uu____3316) with
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
| FStar_Syntax_Syntax.Tm_type (uu____3334) -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3335) -> begin
(

let uu____3336 = (

let uu____3338 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____3338))
in (failwith uu____3336))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3341) -> begin
(

let uu____3364 = (

let uu____3366 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____3366))
in (failwith uu____3364))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3369 = (

let uu____3371 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____3371))
in (failwith uu____3369))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____3375 = (FStar_Syntax_Util.unfold_lazy i)
in (translate_term_to_mlty env uu____3375))
end
| FStar_Syntax_Syntax.Tm_constant (uu____3376) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3377) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3384) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____3398) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____3403; FStar_Syntax_Syntax.index = uu____3404; FStar_Syntax_Syntax.sort = t2}, uu____3406) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____3415) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3421, uu____3422) -> begin
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

let uu____3495 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3495) with
| (bs1, c1) -> begin
(

let uu____3502 = (binders_as_ml_binders env bs1)
in (match (uu____3502) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.env_tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let c2 = (comp_no_args c1)
in (

let uu____3535 = (

let uu____3542 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.env_tcenv eff)
in (FStar_Util.must uu____3542))
in (match (uu____3535) with
| (ed, qualifiers) -> begin
(

let uu____3563 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____3563) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.env_tcenv c2 FStar_Syntax_Syntax.U_unknown)
in ((FStar_Extraction_ML_UEnv.debug env1 (fun uu____3571 -> (

let uu____3572 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____3574 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Translating comp type %s as %s\n" uu____3572 uu____3574)))));
(

let res = (translate_term_to_mlty env1 t2)
in ((FStar_Extraction_ML_UEnv.debug env1 (fun uu____3583 -> (

let uu____3584 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____3586 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____3588 = (FStar_Extraction_ML_Code.string_of_mlty env1.FStar_Extraction_ML_UEnv.currentModule res)
in (FStar_Util.print3 "Translated comp type %s as %s ... to %s\n" uu____3584 uu____3586 uu____3588))))));
res;
));
))
end
| uu____3591 -> begin
(translate_term_to_mlty env1 (FStar_Syntax_Util.comp_result c2))
end))
end))))
in (

let erase = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____3594 = (FStar_List.fold_right (fun uu____3614 uu____3615 -> (match (((uu____3614), (uu____3615))) with
| ((uu____3638, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (uu____3594) with
| (uu____3653, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____3682 = (

let uu____3683 = (FStar_Syntax_Util.un_uinst head1)
in uu____3683.FStar_Syntax_Syntax.n)
in (match (uu____3682) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____3714 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (translate_term_to_mlty env uu____3714))
end
| uu____3735 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____3738) -> begin
(

let uu____3763 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____3763) with
| (bs1, ty1) -> begin
(

let uu____3770 = (binders_as_ml_binders env bs1)
in (match (uu____3770) with
| (bts, env1) -> begin
(translate_term_to_mlty env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_let (uu____3798) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____3812) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
in (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____3844) -> begin
(

let uu____3851 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____3851) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____3857 -> begin
false
end))
in (

let uu____3859 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv t0)
in (match (uu____3859) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| uu____3862 -> begin
(

let mlt = (aux g t0)
in (

let uu____3865 = (is_top_ty mlt)
in (match (uu____3865) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::basic_norm_steps) g.FStar_Extraction_ML_UEnv.env_tcenv t0)
in (aux g t))
end
| uu____3869 -> begin
mlt
end)))
end)))))))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.uenv) = (fun g bs -> (

let uu____3884 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____3940 b -> (match (uu____3940) with
| (ml_bs, env) -> begin
(

let uu____3986 = (is_type_binder g b)
in (match (uu____3986) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____4012 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____4012), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____4027 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (translate_term_to_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____4033 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____4033) with
| (env1, b2, uu____4058) -> begin
(

let ml_b = (

let uu____4067 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____4067), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____3884) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let term_as_mlty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize basic_norm_steps g.FStar_Extraction_ML_UEnv.env_tcenv t0)
in (translate_term_to_mlty g t)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____4163) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____4166, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____4170 -> begin
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
| uu____4199 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____4204 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____4205 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____4206 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____4215 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____4243 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____4243) with
| true -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____4246 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____4277 -> begin
p
end)
end))
end
| uu____4280 -> begin
p
end))


let rec extract_one_pat : Prims.bool  ->  FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option  ->  (FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.uenv * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.list) FStar_Pervasives_Native.option * Prims.bool) = (fun imp g p expected_topt term_as_mlexpr -> (

let ok = (fun t -> (match (expected_topt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let ok = (type_leq g t t')
in ((match ((not (ok))) with
| true -> begin
(FStar_Extraction_ML_UEnv.debug g (fun uu____4382 -> (

let uu____4383 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____4385 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____4383 uu____4385)))))
end
| uu____4388 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, swopt)) when (

let uu____4421 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____4421 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))) -> begin
(

let uu____4426 = (match (swopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4439 = (

let uu____4440 = (

let uu____4441 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (((c), (FStar_Pervasives_Native.None)))))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4441))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____4440))
in ((uu____4439), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end
| FStar_Pervasives_Native.Some (sw) -> begin
(

let source_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer g.FStar_Extraction_ML_UEnv.env_tcenv.FStar_TypeChecker_Env.dsenv c sw FStar_Range.dummyRange)
in (

let uu____4463 = (term_as_mlexpr g source_term)
in (match (uu____4463) with
| (mlterm, uu____4475, mlty) -> begin
((mlterm), (mlty))
end)))
end)
in (match (uu____4426) with
| (mlc, ml_ty) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____4497 = (

let uu____4498 = (

let uu____4505 = (

let uu____4508 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ml_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____4508)::(mlc)::[])
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____4505)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4498))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____4497))
in (

let uu____4511 = (ok ml_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____4511)))))
end))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant g.FStar_Extraction_ML_UEnv.env_tcenv FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____4533 = (

let uu____4542 = (

let uu____4549 = (

let uu____4550 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____4550))
in ((uu____4549), ([])))
in FStar_Pervasives_Native.Some (uu____4542))
in (

let uu____4559 = (ok mlty)
in ((g), (uu____4533), (uu____4559))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____4572 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____4572) with
| (g1, x1, uu____4600) -> begin
(

let uu____4603 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4629 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____4603)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____4641 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____4641) with
| (g1, x1, uu____4669) -> begin
(

let uu____4672 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4698 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____4672)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____4708) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____4751 = (

let uu____4760 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____4760) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____4769; FStar_Extraction_ML_UEnv.exp_b_expr = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____4771; FStar_Extraction_ML_Syntax.loc = uu____4772}; FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____4774} -> begin
((n1), (ttys))
end
| uu____4781 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____4751) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____4818 = (FStar_Util.first_N nTyVars pats)
in (match (uu____4818) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___374_4926 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____4957 -> (match (uu____4957) with
| (p1, uu____4964) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____4967, t) -> begin
(term_as_mlty g t)
end
| uu____4973 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____4977 -> (

let uu____4978 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____4978))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____4982 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____4982))))
end)) (fun uu___373_4996 -> (match (uu___373_4996) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____5011 = (FStar_Util.fold_map (fun g1 uu____5048 -> (match (uu____5048) with
| (p1, imp1) -> begin
(

let uu____5070 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None term_as_mlexpr)
in (match (uu____5070) with
| (g2, p2, uu____5101) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____5011) with
| (g1, tyMLPats) -> begin
(

let uu____5165 = (FStar_Util.fold_map (fun uu____5230 uu____5231 -> (match (((uu____5230), (uu____5231))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____5329 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____5389 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____5329) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____5460 = (extract_one_pat false g2 p1 expected_ty term_as_mlexpr)
in (match (uu____5460) with
| (g3, p2, uu____5503) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____5165) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____5624 = (

let uu____5635 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___368_5686 -> (match (uu___368_5686) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____5728 -> begin
[]
end))))
in (FStar_All.pipe_right uu____5635 FStar_List.split))
in (match (uu____5624) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____5804 -> begin
false
end)
in (

let uu____5814 = (

let uu____5823 = (

let uu____5830 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____5833 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____5830), (uu____5833))))
in FStar_Pervasives_Native.Some (uu____5823))
in ((g2), (uu____5814), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.uenv * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t term_as_mlexpr -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____5965 = (extract_one_pat false g1 p1 expected_t1 term_as_mlexpr)
in (match (uu____5965) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____6028 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____6076 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____6076))
end))
in (

let uu____6077 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____6077) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____6237, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____6241 = (

let uu____6253 = (

let uu____6263 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____6263)))
in (uu____6253)::more_args)
in (eta_args uu____6241 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____6279, uu____6280) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____6305 -> begin
(

let uu____6306 = (

let uu____6308 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr)
in (

let uu____6310 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.format2 "Impossible: Head type is not an arrow: (%s : %s)" uu____6308 uu____6310)))
in (failwith uu____6306))
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____6345, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____6382 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____6404 = (eta_args [] residualType)
in (match (uu____6404) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____6462 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____6462))
end
| uu____6463 -> begin
(

let uu____6475 = (FStar_List.unzip eargs)
in (match (uu____6475) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____6521 = (

let uu____6522 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____6522))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____6521))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____6532 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____6536, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6540; FStar_Extraction_ML_Syntax.loc = uu____6541}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____6564 -> begin
(

let uu____6567 = (

let uu____6574 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____6574), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6567))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6578; FStar_Extraction_ML_Syntax.loc = uu____6579}, uu____6580); FStar_Extraction_ML_Syntax.mlty = uu____6581; FStar_Extraction_ML_Syntax.loc = uu____6582}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____6609 -> begin
(

let uu____6612 = (

let uu____6619 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____6619), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6612))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6623; FStar_Extraction_ML_Syntax.loc = uu____6624}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6632 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6632))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6636; FStar_Extraction_ML_Syntax.loc = uu____6637}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6639))) -> begin
(

let uu____6652 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6652))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6656; FStar_Extraction_ML_Syntax.loc = uu____6657}, uu____6658); FStar_Extraction_ML_Syntax.mlty = uu____6659; FStar_Extraction_ML_Syntax.loc = uu____6660}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6672 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6672))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6676; FStar_Extraction_ML_Syntax.loc = uu____6677}, uu____6678); FStar_Extraction_ML_Syntax.mlty = uu____6679; FStar_Extraction_ML_Syntax.loc = uu____6680}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6682))) -> begin
(

let uu____6699 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6699))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6705 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6705))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6709))) -> begin
(

let uu____6718 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6718))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6722; FStar_Extraction_ML_Syntax.loc = uu____6723}, uu____6724), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6731 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6731))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6735; FStar_Extraction_ML_Syntax.loc = uu____6736}, uu____6737), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6738))) -> begin
(

let uu____6751 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6751))
end
| uu____6754 -> begin
mlAppExpr
end)))))


let maybe_promote_effect : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag) = (fun ml_e tag t -> (match (((tag), (t))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| uu____6785 -> begin
((ml_e), (tag))
end))


let extract_lb_sig : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.letbindings  ->  (FStar_Syntax_Syntax.lbname * FStar_Extraction_ML_Syntax.e_tag * (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.binders * FStar_Extraction_ML_Syntax.mltyscheme)) * Prims.bool * FStar_Syntax_Syntax.term) Prims.list = (fun g lbs -> (

let maybe_generalize = (fun uu____6846 -> (match (uu____6846) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____6867; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu____6871; FStar_Syntax_Syntax.lbpos = uu____6872} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let lbtyp1 = (FStar_Syntax_Subst.compress lbtyp)
in (

let no_gen = (fun uu____6953 -> (

let expected_t = (term_as_mlty g lbtyp1)
in ((lbname_), (f_e), (((lbtyp1), ((([]), ((([]), (expected_t))))))), (false), (lbdef))))
in (

let uu____7030 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1)
in (match (uu____7030) with
| true -> begin
((lbname_), (f_e), (((lbtyp1), ((([]), ((([]), (FStar_Extraction_ML_Syntax.MLTY_Erased))))))), (false), (lbdef))
end
| uu____7073 -> begin
(match (lbtyp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____7116 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____7116 (is_type_binder g))) -> begin
(

let uu____7138 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7138) with
| (bs1, c1) -> begin
(

let uu____7164 = (

let uu____7177 = (FStar_Util.prefix_until (fun x -> (

let uu____7223 = (is_type_binder g x)
in (not (uu____7223)))) bs1)
in (match (uu____7177) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____7350 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____7350)))
end))
in (match (uu____7164) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let lbdef1 = (

let uu____7412 = (normalize_abs lbdef)
in (FStar_All.pipe_right uu____7412 FStar_Syntax_Util.unmeta))
in (match (lbdef1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____7461 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____7461) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____7519 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____7519) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____7626 uu____7627 -> (match (((uu____7626), (uu____7627))) with
| ((x, uu____7653), (y, uu____7655)) -> begin
(

let uu____7676 = (

let uu____7683 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____7683)))
in FStar_Syntax_Syntax.NT (uu____7676))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____7700 -> (match (uu____7700) with
| (a, uu____7708) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____7719 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____7738 -> (match (uu____7738) with
| (x, uu____7747) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____7719), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
((

let uu____7763 = (is_fstar_value body1)
in (not (uu____7763))) || (

let uu____7766 = (FStar_Syntax_Util.is_pure_comp c1)
in (not (uu____7766))))
end
| uu____7768 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____7786 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____7790 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((lbtyp1), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____7808 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____7830) -> begin
(

let env = (FStar_List.fold_left (fun env uu____7849 -> (match (uu____7849) with
| (a, uu____7857) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____7868 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____7887 -> (match (uu____7887) with
| (x, uu____7896) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____7868), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____7940 -> (match (uu____7940) with
| (bv, uu____7948) -> begin
(

let uu____7953 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____7953 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7983) -> begin
(

let env = (FStar_List.fold_left (fun env uu____7996 -> (match (uu____7996) with
| (a, uu____8004) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8015 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8034 -> (match (uu____8034) with
| (x, uu____8043) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8015), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8087 -> (match (uu____8087) with
| (bv, uu____8095) -> begin
(

let uu____8100 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8100 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____8130) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8143 -> (match (uu____8143) with
| (a, uu____8151) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8162 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8181 -> (match (uu____8181) with
| (x, uu____8190) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8162), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8234 -> (match (uu____8234) with
| (bv, uu____8242) -> begin
(

let uu____8247 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8247 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| uu____8277 -> begin
(err_value_restriction lbdef1)
end)))
end))
end))
end
| uu____8297 -> begin
(no_gen ())
end)
end)))))
end))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map maybe_generalize))))


let extract_lb_iface : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.letbindings  ->  (FStar_Extraction_ML_UEnv.uenv * (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list) = (fun g lbs -> (

let is_top = (FStar_Syntax_Syntax.is_top_level (FStar_Pervasives_Native.snd lbs))
in (

let is_rec = ((not (is_top)) && (FStar_Pervasives_Native.fst lbs))
in (

let lbs1 = (extract_lb_sig g lbs)
in (FStar_Util.fold_map (fun env uu____8448 -> (match (uu____8448) with
| (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body) -> begin
(

let uu____8509 = (FStar_Extraction_ML_UEnv.extend_lb env lbname typ mltyscheme add_unit is_rec)
in (match (uu____8509) with
| (env1, uu____8526, exp_binding) -> begin
(

let uu____8530 = (

let uu____8535 = (FStar_Util.right lbname)
in ((uu____8535), (exp_binding)))
in ((env1), (uu____8530)))
end))
end)) g lbs1)))))


let rec check_term_as_mlexpr : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e f ty -> ((FStar_Extraction_ML_UEnv.debug g (fun uu____8601 -> (

let uu____8602 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____8604 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.print2 "Checking %s at type %s\n" uu____8602 uu____8604)))));
(match (((f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____8611) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____8612 -> begin
(

let uu____8617 = (term_as_mlexpr g e)
in (match (uu____8617) with
| (ml_e, tag, t) -> begin
(

let uu____8631 = (maybe_promote_effect ml_e tag t)
in (match (uu____8631) with
| (ml_e1, tag1) -> begin
(

let uu____8642 = (FStar_Extraction_ML_Util.eff_leq tag1 f)
in (match (uu____8642) with
| true -> begin
(

let uu____8649 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____8649), (ty)))
end
| uu____8650 -> begin
(match (((tag1), (f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(

let uu____8656 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____8656), (ty)))
end
| uu____8657 -> begin
((err_unexpected_eff g e ty f tag1);
(

let uu____8665 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____8665), (ty)));
)
end)
end))
end))
end))
end);
))
and term_as_mlexpr : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let uu____8668 = (term_as_mlexpr' g e)
in (match (uu____8668) with
| (e1, f, t) -> begin
(

let uu____8684 = (maybe_promote_effect e1 f t)
in (match (uu____8684) with
| (e2, f1) -> begin
((e2), (f1), (t))
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____8709 = (

let uu____8711 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____8713 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____8715 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____8711 uu____8713 uu____8715))))
in (FStar_Util.print_string uu____8709))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____8725 = (

let uu____8727 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8727))
in (failwith uu____8725))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____8736) -> begin
(

let uu____8759 = (

let uu____8761 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8761))
in (failwith uu____8759))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____8770) -> begin
(

let uu____8783 = (

let uu____8785 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8785))
in (failwith uu____8783))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____8794) -> begin
(

let uu____8795 = (

let uu____8797 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8797))
in (failwith uu____8795))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____8807 = (FStar_Syntax_Util.unfold_lazy i)
in (term_as_mlexpr g uu____8807))
end
| FStar_Syntax_Syntax.Tm_type (uu____8808) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____8809) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____8816) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____8832}) -> begin
(

let uu____8845 = (

let uu____8846 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____8846))
in (match (uu____8845) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____8853; FStar_Extraction_ML_UEnv.exp_b_expr = fw; FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____8855; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____8856} -> begin
(

let uu____8859 = (

let uu____8860 = (

let uu____8861 = (

let uu____8868 = (

let uu____8871 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Cannot evaluate open quotation at runtime"))))
in (uu____8871)::[])
in ((fw), (uu____8868)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____8861))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____8860))
in ((uu____8859), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) -> begin
(

let uu____8889 = (FStar_Reflection_Basic.inspect_ln qt)
in (match (uu____8889) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____8897 = (FStar_Syntax_Syntax.lookup_aq bv aqs)
in (match (uu____8897) with
| FStar_Pervasives_Native.Some (tm) -> begin
(term_as_mlexpr g tm)
end
| FStar_Pervasives_Native.None -> begin
(

let tv = (

let uu____8908 = (

let uu____8915 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____8915 (FStar_Reflection_Data.Tv_Var (bv))))
in (uu____8908 t.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in (

let t1 = (

let uu____8946 = (

let uu____8957 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____8957)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____8946))
in (term_as_mlexpr g t1)))
end))
end
| tv -> begin
(

let tv1 = (

let uu____8984 = (

let uu____8991 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____8991 tv))
in (uu____8984 t.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in (

let t1 = (

let uu____9022 = (

let uu____9033 = (FStar_Syntax_Syntax.as_arg tv1)
in (uu____9033)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____9022))
in (term_as_mlexpr g t1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____9060)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____9093 = (

let uu____9100 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.env_tcenv m)
in (FStar_Util.must uu____9100))
in (match (uu____9093) with
| (ed, qualifiers) -> begin
(

let uu____9127 = (

let uu____9129 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname)
in (not (uu____9129)))
in (match (uu____9127) with
| true -> begin
(term_as_mlexpr g t2)
end
| uu____9138 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____9147 -> begin
(term_as_mlexpr g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____9149) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____9155) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____9161 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (match (uu____9161) with
| (uu____9174, ty, uu____9176) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____9178 = (

let uu____9179 = (FStar_Extraction_ML_Util.mlexpr_of_const t.FStar_Syntax_Syntax.pos c)
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9179))
in ((uu____9178), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____9180) -> begin
(

let uu____9181 = (is_type g t)
in (match (uu____9181) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____9190 -> begin
(

let uu____9192 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____9192) with
| (FStar_Util.Inl (uu____9205), uu____9206) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr ({FStar_Extraction_ML_UEnv.exp_b_name = uu____9211; FStar_Extraction_ML_UEnv.exp_b_expr = x; FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9214}), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____9232 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____9232), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____9233 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9241 = (is_type g t)
in (match (uu____9241) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____9250 -> begin
(

let uu____9252 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____9252) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_UEnv.exp_b_name = uu____9261; FStar_Extraction_ML_UEnv.exp_b_expr = x; FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9264}) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____9272 -> (

let uu____9273 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____9275 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule x)
in (

let uu____9277 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule (FStar_Pervasives_Native.snd mltys))
in (FStar_Util.print3 "looked up %s: got %s at %s \n" uu____9273 uu____9275 uu____9277))))));
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____9290 = (maybe_eta_data_and_project_record g fv.FStar_Syntax_Syntax.fv_qual t1 x)
in ((uu____9290), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____9291 -> begin
(err_uninst g t mltys t)
end);
)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, rcopt) -> begin
(

let uu____9325 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____9325) with
| (bs1, body1) -> begin
(

let uu____9338 = (binders_as_ml_binders g bs1)
in (match (uu____9338) with
| (ml_bs, env) -> begin
(

let body2 = (match (rcopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____9374 = (FStar_TypeChecker_Env.is_reifiable_rc env.FStar_Extraction_ML_UEnv.env_tcenv rc)
in (match (uu____9374) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.env_tcenv body1)
end
| uu____9377 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____9382 -> (

let uu____9383 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____9383))));
body1;
)
end)
in (

let uu____9386 = (term_as_mlexpr env body2)
in (match (uu____9386) with
| (ml_body, f, t1) -> begin
(

let uu____9402 = (FStar_List.fold_right (fun uu____9422 uu____9423 -> (match (((uu____9422), (uu____9423))) with
| ((uu____9446, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____9402) with
| (f1, tfun) -> begin
(

let uu____9469 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____9469), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____9477; FStar_Syntax_Syntax.vars = uu____9478}, ((a1, uu____9480))::[]) -> begin
(

let ty = (

let uu____9520 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (term_as_mlty g uu____9520))
in (

let uu____9521 = (

let uu____9522 = (FStar_Extraction_ML_Util.mlexpr_of_range a1.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) uu____9522))
in ((uu____9521), (FStar_Extraction_ML_Syntax.E_PURE), (ty))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____9523; FStar_Syntax_Syntax.vars = uu____9524}, ((t1, uu____9526))::((r, uu____9528))::[]) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____9583)); FStar_Syntax_Syntax.pos = uu____9584; FStar_Syntax_Syntax.vars = uu____9585}, uu____9586) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___369_9655 -> (match (uu___369_9655) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____9658 -> begin
false
end))))))
in (

let uu____9660 = (

let uu____9665 = (

let uu____9666 = (FStar_Syntax_Subst.compress head1)
in uu____9666.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____9665)))
in (match (uu____9660) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____9675), uu____9676) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____9690, FStar_Syntax_Syntax.Tm_abs (bs, uu____9692, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____9717, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____9719 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____9719))
in (

let tm = (

let uu____9731 = (

let uu____9736 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____9737 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____9736 uu____9737)))
in (uu____9731 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr g tm)))
end
| uu____9748 -> begin
(

let rec extract_app = (fun is_data uu____9801 uu____9802 restArgs -> (match (((uu____9801), (uu____9802))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(

let mk_head = (fun uu____9883 -> (

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____9910 -> (

let uu____9911 = (

let uu____9913 = (mk_head ())
in (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule uu____9913))
in (

let uu____9914 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t1)
in (

let uu____9916 = (match (restArgs) with
| [] -> begin
"none"
end
| ((hd1, uu____9927))::uu____9928 -> begin
(FStar_Syntax_Print.term_to_string hd1)
end)
in (FStar_Util.print3 "extract_app ml_head=%s type of head = %s, next arg = %s\n" uu____9911 uu____9914 uu____9916))))));
(match (((restArgs), (t1))) with
| ([], uu____9962) -> begin
(

let app = (

let uu____9978 = (mk_head ())
in (maybe_eta_data_and_project_record g is_data t1 uu____9978))
in ((app), (f), (t1)))
end
| (((arg, uu____9980))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____10011 = (

let uu____10016 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____10016), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____10011 rest))
end
| (((e0, uu____10028))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let expected_effect = (

let uu____10061 = ((FStar_Options.lax ()) && (FStar_TypeChecker_Util.short_circuit_head head1))
in (match (uu____10061) with
| true -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| uu____10064 -> begin
FStar_Extraction_ML_Syntax.E_PURE
end))
in (

let uu____10066 = (check_term_as_mlexpr g e0 expected_effect tExpected)
in (match (uu____10066) with
| (e01, tInferred) -> begin
(

let uu____10079 = (

let uu____10084 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::[]))
in ((uu____10084), (t2)))
in (extract_app is_data ((mlhead), ((((e01), (expected_effect)))::mlargs_f)) uu____10079 rest))
end))))
end
| uu____10095 -> begin
(

let uu____10108 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____10108) with
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
| uu____10180 -> begin
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

let extract_app_maybe_projector = (fun is_data mlhead uu____10251 args1 -> (match (uu____10251) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____10281)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10365))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____10367, f', t3)) -> begin
(

let uu____10405 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____10405 t3))
end
| uu____10406 -> begin
((args2), (f1), (t2))
end))
in (

let uu____10431 = (remove_implicits args1 f t1)
in (match (uu____10431) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____10487 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let extract_app_with_instantiations = (fun uu____10511 -> (

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (uu____10519) -> begin
(

let uu____10520 = (

let uu____10541 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____10541) with
| (FStar_Util.Inr (exp_b), q) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____10580 -> (

let uu____10581 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____10583 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule exp_b.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____10585 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule (FStar_Pervasives_Native.snd exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme))
in (

let uu____10587 = (FStar_Util.string_of_bool exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.print4 "@@@looked up %s: got %s at %s (inst_ok=%s)\n" uu____10581 uu____10583 uu____10585 uu____10587)))))));
((((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr), (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme), (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok))), (q));
)
end
| uu____10614 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____10520) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____10690))::uu____10691 -> begin
(is_type g a)
end
| uu____10718 -> begin
false
end)
in (

let uu____10730 = (match (vars) with
| (uu____10759)::uu____10760 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____10774 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____10809 = (FStar_Util.first_N n1 args)
in (match (uu____10809) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____10914 -> (match (uu____10914) with
| (x, uu____10922) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____10934 -> (

let uu____10935 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____10937 = (FStar_Syntax_Print.args_to_string prefix1)
in (

let uu____10939 = (

let uu____10941 = (FStar_List.map (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule) prefixAsMLTypes)
in (FStar_All.pipe_right uu____10941 (FStar_String.concat ", ")))
in (

let uu____10951 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t2)
in (FStar_Util.print4 "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n" uu____10935 uu____10937 uu____10939 uu____10951)))))));
(

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____10969 -> begin
(

let uu___375_10972 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___375_10972.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___375_10972.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____10976) -> begin
(

let uu___376_10977 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___376_10977.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___376_10977.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____10978) -> begin
(

let uu___376_10980 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___376_10980.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___376_10980.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____10982; FStar_Extraction_ML_Syntax.loc = uu____10983})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___377_10989 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___377_10989.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___377_10989.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____10990 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))));
)))
end))
end
| uu____11000 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____10730) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____11056 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____11056), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____11057 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____11066) -> begin
(

let uu____11067 = (

let uu____11088 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____11088) with
| (FStar_Util.Inr (exp_b), q) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____11127 -> (

let uu____11128 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____11130 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule exp_b.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____11132 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule (FStar_Pervasives_Native.snd exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme))
in (

let uu____11134 = (FStar_Util.string_of_bool exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.print4 "@@@looked up %s: got %s at %s (inst_ok=%s)\n" uu____11128 uu____11130 uu____11132 uu____11134)))))));
((((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr), (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme), (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok))), (q));
)
end
| uu____11161 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____11067) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____11237))::uu____11238 -> begin
(is_type g a)
end
| uu____11265 -> begin
false
end)
in (

let uu____11277 = (match (vars) with
| (uu____11306)::uu____11307 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____11321 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____11356 = (FStar_Util.first_N n1 args)
in (match (uu____11356) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____11461 -> (match (uu____11461) with
| (x, uu____11469) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____11481 -> (

let uu____11482 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____11484 = (FStar_Syntax_Print.args_to_string prefix1)
in (

let uu____11486 = (

let uu____11488 = (FStar_List.map (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule) prefixAsMLTypes)
in (FStar_All.pipe_right uu____11488 (FStar_String.concat ", ")))
in (

let uu____11498 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t2)
in (FStar_Util.print4 "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n" uu____11482 uu____11484 uu____11486 uu____11498)))))));
(

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____11516 -> begin
(

let uu___375_11519 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___375_11519.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___375_11519.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____11523) -> begin
(

let uu___376_11524 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___376_11524.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___376_11524.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____11525) -> begin
(

let uu___376_11527 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___376_11527.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___376_11527.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____11529; FStar_Extraction_ML_Syntax.loc = uu____11530})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___377_11536 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___377_11536.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___377_11536.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____11537 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))));
)))
end))
end
| uu____11547 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____11277) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____11603 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____11603), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____11604 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____11613 -> begin
(

let uu____11614 = (term_as_mlexpr g head2)
in (match (uu____11614) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end)))
in (

let uu____11630 = (is_type g t)
in (match (uu____11630) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____11639 -> begin
(

let uu____11641 = (

let uu____11642 = (FStar_Syntax_Util.un_uinst head1)
in uu____11642.FStar_Syntax_Syntax.n)
in (match (uu____11641) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11652 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____11652) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____11661 -> begin
(extract_app_with_instantiations ())
end))
end
| uu____11664 -> begin
(extract_app_with_instantiations ())
end))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____11667), f) -> begin
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

let uu____11735 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____11735) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____11770 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____11784 -> begin
(

let uu____11786 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____11786) with
| true -> begin
((lbs), (e'))
end
| uu____11797 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____11801 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____11801))
in (

let lb1 = (

let uu___378_11803 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___378_11803.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___378_11803.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___378_11803.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___378_11803.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___378_11803.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___378_11803.FStar_Syntax_Syntax.lbpos})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____11770) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____11837 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.env_tcenv uu____11837))
in (

let lbdef = (

let uu____11852 = (FStar_Options.ml_ish ())
in (match (uu____11852) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____11857 -> begin
(

let norm_call = (fun uu____11864 -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.PureSubtermsWithinComputations)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.ForExtraction)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef))
in (

let uu____11865 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("Extraction"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("ExtractNorm"))))
in (match (uu____11865) with
| true -> begin
((

let uu____11875 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____11877 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Util.print2 "Starting to normalize top-level let %s)\n\tlbdef=%s" uu____11875 uu____11877)));
(

let a = (

let uu____11883 = (

let uu____11885 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.format1 "###(Time to normalize top-level let %s)" uu____11885))
in (FStar_Util.measure_execution_time uu____11883 norm_call))
in ((

let uu____11891 = (FStar_Syntax_Print.term_to_string a)
in (FStar_Util.print1 "Normalized to %s\n" uu____11891));
a;
));
)
end
| uu____11894 -> begin
(norm_call ())
end)))
end))
in (

let uu___379_11896 = lb
in {FStar_Syntax_Syntax.lbname = uu___379_11896.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___379_11896.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___379_11896.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___379_11896.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___379_11896.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___379_11896.FStar_Syntax_Syntax.lbpos}))))))
end
| uu____11897 -> begin
lbs1
end)
in (

let check_lb = (fun env uu____11949 -> (match (uu____11949) with
| (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____12105 -> (match (uu____12105) with
| (a, uu____12113) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____12119 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____12119) with
| (e1, ty) -> begin
(

let uu____12130 = (maybe_promote_effect e1 f expected_t)
in (match (uu____12130) with
| (e2, f1) -> begin
(

let meta = (match (((f1), (ty))) with
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| uu____12142 -> begin
[]
end)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e2; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = true})))
end))
end))))
end))
in (

let lbs3 = (extract_lb_sig g ((is_rec), (lbs2)))
in (

let uu____12173 = (FStar_List.fold_right (fun lb uu____12270 -> (match (uu____12270) with
| (env, lbs4) -> begin
(

let uu____12404 = lb
in (match (uu____12404) with
| (lbname, uu____12455, (t1, (uu____12457, polytype)), add_unit, uu____12460) -> begin
(

let uu____12475 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____12475) with
| (env1, nm, uu____12516) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____12173) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____12701 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____12795 = (term_as_mlexpr env_body e'1)
in (match (uu____12795) with
| (e'2, f', t') -> begin
(

let f = (

let uu____12812 = (

let uu____12815 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____12815)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____12812))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____12826 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____12828 = (

let uu____12829 = (

let uu____12830 = (

let uu____12831 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), (uu____12831)))
in (mk_MLE_Let top_level uu____12830 e'2))
in (

let uu____12840 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____12829 uu____12840)))
in ((uu____12828), (f), (t')))))
end)))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____12879 = (term_as_mlexpr g scrutinee)
in (match (uu____12879) with
| (e, f_e, t_e) -> begin
(

let uu____12895 = (check_pats_for_ite pats)
in (match (uu____12895) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____12960 = (term_as_mlexpr g then_e1)
in (match (uu____12960) with
| (then_mle, f_then, t_then) -> begin
(

let uu____12976 = (term_as_mlexpr g else_e1)
in (match (uu____12976) with
| (else_mle, f_else, t_else) -> begin
(

let uu____12992 = (

let uu____13003 = (type_leq g t_then t_else)
in (match (uu____13003) with
| true -> begin
((t_else), (no_lift))
end
| uu____13022 -> begin
(

let uu____13024 = (type_leq g t_else t_then)
in (match (uu____13024) with
| true -> begin
((t_then), (no_lift))
end
| uu____13043 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____12992) with
| (t_branch, maybe_lift1) -> begin
(

let uu____13071 = (

let uu____13072 = (

let uu____13073 = (

let uu____13082 = (maybe_lift1 then_mle t_then)
in (

let uu____13083 = (

let uu____13086 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____13086))
in ((e), (uu____13082), (uu____13083))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____13073))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____13072))
in (

let uu____13089 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____13071), (uu____13089), (t_branch))))
end))
end))
end))
end
| uu____13090 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____13106 -> begin
(

let uu____13108 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____13207 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____13207) with
| (pat, when_opt, branch1) -> begin
(

let uu____13252 = (extract_pat g pat t_e term_as_mlexpr)
in (match (uu____13252) with
| (env, p, pat_t_compat) -> begin
(

let uu____13314 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let w_pos = w.FStar_Syntax_Syntax.pos
in (

let uu____13337 = (term_as_mlexpr env w)
in (match (uu____13337) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce w_pos env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end)))
end)
in (match (uu____13314) with
| (when_opt1, f_when) -> begin
(

let uu____13387 = (term_as_mlexpr env branch1)
in (match (uu____13387) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____13422 = (FStar_All.pipe_right p (FStar_List.map (fun uu____13499 -> (match (uu____13499) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____13422)))
end))
end))
end))
end))) true))
in (match (uu____13108) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____13664 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____13670 -> (

let uu____13671 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____13673 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____13671 uu____13673)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____13700 = (

let uu____13701 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____13701))
in (match (uu____13700) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____13708; FStar_Extraction_ML_UEnv.exp_b_expr = fw; FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____13710; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____13711} -> begin
(

let uu____13714 = (

let uu____13715 = (

let uu____13716 = (

let uu____13723 = (

let uu____13726 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____13726)::[])
in ((fw), (uu____13723)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____13716))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____13715))
in ((uu____13714), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| ((uu____13730, uu____13731, (uu____13732, f_first, t_first)))::rest -> begin
(

let uu____13792 = (FStar_List.fold_left (fun uu____13834 uu____13835 -> (match (((uu____13834), (uu____13835))) with
| ((topt, f), (uu____13892, uu____13893, (uu____13894, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____13950 = (type_leq g t1 t_branch)
in (match (uu____13950) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____13955 -> begin
(

let uu____13957 = (type_leq g t_branch t1)
in (match (uu____13957) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____13962 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____13792) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____14055 -> (match (uu____14055) with
| (p, (wopt, uu____14084), (b1, uu____14086, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____14105) -> begin
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

let uu____14110 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____14110), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____14137 = (

let uu____14142 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.env_tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14142))
in (match (uu____14137) with
| (uu____14167, fstar_disc_type) -> begin
(

let wildcards = (

let uu____14177 = (

let uu____14178 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____14178.FStar_Syntax_Syntax.n)
in (match (uu____14177) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____14189) -> begin
(

let uu____14210 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___370_14244 -> (match (uu___370_14244) with
| (uu____14252, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____14253))) -> begin
true
end
| uu____14258 -> begin
false
end))))
in (FStar_All.pipe_right uu____14210 (FStar_List.map (fun uu____14294 -> (

let uu____14301 = (fresh "_")
in ((uu____14301), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____14305 -> begin
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

let uu____14320 = (

let uu____14321 = (

let uu____14333 = (

let uu____14334 = (

let uu____14335 = (

let uu____14350 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____14356 = (

let uu____14367 = (

let uu____14376 = (

let uu____14377 = (

let uu____14384 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____14384), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____14377))
in (

let uu____14387 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____14376), (FStar_Pervasives_Native.None), (uu____14387))))
in (

let uu____14391 = (

let uu____14402 = (

let uu____14411 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____14411)))
in (uu____14402)::[])
in (uu____14367)::uu____14391))
in ((uu____14350), (uu____14356))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____14335))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____14334))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____14333)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____14321))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____14320))
in (

let uu____14472 = (

let uu____14473 = (

let uu____14476 = (

let uu____14477 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____14477; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____14476)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), (uu____14473)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____14472)))))))
end)))




