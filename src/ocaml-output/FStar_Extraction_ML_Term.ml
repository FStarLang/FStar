
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


let err_ill_typed_application : 'Auu____199 'Auu____200 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * 'Auu____199) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____200 = (fun env t args ty -> (

let uu____233 = (

let uu____238 = (

let uu____239 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____240 = (

let uu____241 = (FStar_All.pipe_right args (FStar_List.map (fun uu____259 -> (match (uu____259) with
| (x, uu____265) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____241 (FStar_String.concat " ")))
in (

let uu____268 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" uu____239 uu____240 uu____268))))
in ((FStar_Errors.Fatal_IllTyped), (uu____238)))
in (fail t.FStar_Syntax_Syntax.pos uu____233)))


let err_ill_typed_erasure : 'Auu____277 . FStar_Extraction_ML_UEnv.env  ->  FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____277 = (fun env pos ty -> (

let uu____293 = (

let uu____298 = (

let uu____299 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format1 "Erased value found where a value of type %s was expected" uu____299))
in ((FStar_Errors.Fatal_IllTyped), (uu____298)))
in (fail pos uu____293)))


let err_value_restriction : 'Auu____304 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____304 = (fun t -> (

let uu____314 = (

let uu____319 = (

let uu____320 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____321 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____320 uu____321)))
in ((FStar_Errors.Fatal_ValueRestriction), (uu____319)))
in (fail t.FStar_Syntax_Syntax.pos uu____314)))


let err_unexpected_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  unit = (fun env t ty f0 f1 -> (

let uu____351 = (

let uu____356 = (

let uu____357 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____358 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____359 = (FStar_Extraction_ML_Util.eff_to_string f0)
in (

let uu____360 = (FStar_Extraction_ML_Util.eff_to_string f1)
in (FStar_Util.format4 "for expression %s of type %s, Expected effect %s; got effect %s" uu____357 uu____358 uu____359 uu____360)))))
in ((FStar_Errors.Warning_ExtractionUnexpectedEffect), (uu____356)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____351)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____383 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____383) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____388 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____388) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____399, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (

let uu____409 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)
in (match (uu____409) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____410 -> begin
(

let uu____411 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____411) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____412 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____434 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____434) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____437 -> begin
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

let uu____455 = (

let uu____456 = (FStar_Syntax_Subst.compress t1)
in uu____456.FStar_Syntax_Syntax.n)
in (match (uu____455) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____459) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____484) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____511) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____519 = (FStar_Syntax_Util.unfold_lazy i)
in (is_arity env uu____519))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____520) -> begin
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
| FStar_Syntax_Syntax.Tm_fvar (uu____566) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____568 = (

let uu____569 = (FStar_Syntax_Subst.compress t2)
in uu____569.FStar_Syntax_Syntax.n)
in (match (uu____568) with
| FStar_Syntax_Syntax.Tm_fvar (uu____572) -> begin
false
end
| uu____573 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____574) -> begin
(

let uu____589 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____589) with
| (head1, uu____605) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____627) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____633) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____638, body, uu____640) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____661, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____679, branches) -> begin
(match (branches) with
| ((uu____717, uu____718, e))::uu____720 -> begin
(is_arity env e)
end
| uu____767 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____795) -> begin
(

let uu____820 = (

let uu____821 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____821))
in (failwith uu____820))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____822 = (

let uu____823 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____823))
in (failwith uu____822))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____825 = (FStar_Syntax_Util.unfold_lazy i)
in (is_type_aux env uu____825))
end
| FStar_Syntax_Syntax.Tm_constant (uu____826) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____827) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____828) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____835) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____850, t2) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____876; FStar_Syntax_Syntax.index = uu____877; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____881; FStar_Syntax_Syntax.index = uu____882; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____887, uu____888) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____930) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____937) -> begin
(

let uu____958 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____958) with
| (uu____963, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____980 = (

let uu____985 = (

let uu____986 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____986)::[])
in (FStar_Syntax_Subst.open_term uu____985 body))
in (match (uu____980) with
| (uu____987, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____989, lbs), body) -> begin
(

let uu____1006 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____1006) with
| (uu____1013, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____1019, branches) -> begin
(match (branches) with
| (b)::uu____1058 -> begin
(

let uu____1103 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____1103) with
| (uu____1104, uu____1105, e) -> begin
(is_type_aux env e)
end))
end
| uu____1123 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1140) -> begin
false
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1148) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1154) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1189 -> (

let uu____1190 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1191 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1190 uu____1191)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1197 -> (match (b) with
| true -> begin
(

let uu____1198 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1199 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____1198 uu____1199)))
end
| uu____1200 -> begin
(

let uu____1201 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1202 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1201 uu____1202)))
end)));
b;
));
))


let is_type_binder : 'Auu____1209 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____1209)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1233 = (

let uu____1234 = (FStar_Syntax_Subst.compress t)
in uu____1234.FStar_Syntax_Syntax.n)
in (match (uu____1233) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1237; FStar_Syntax_Syntax.fv_delta = uu____1238; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1239; FStar_Syntax_Syntax.fv_delta = uu____1240; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1241))}) -> begin
true
end
| uu____1248 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1254 = (

let uu____1255 = (FStar_Syntax_Subst.compress t)
in uu____1255.FStar_Syntax_Syntax.n)
in (match (uu____1254) with
| FStar_Syntax_Syntax.Tm_constant (uu____1258) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1259) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1260) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1261) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1300 = (is_constructor head1)
in (match (uu____1300) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1316 -> (match (uu____1316) with
| (te, uu____1322) -> begin
(is_fstar_value te)
end))))
end
| uu____1323 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1325) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1331, uu____1332) -> begin
(is_fstar_value t1)
end
| uu____1373 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1379) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1380) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1381) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1382) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1393, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1402, fields) -> begin
(FStar_Util.for_all (fun uu____1427 -> (match (uu____1427) with
| (uu____1432, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1435) -> begin
(is_ml_value h)
end
| uu____1440 -> begin
false
end))


let fresh : Prims.string  ->  Prims.string = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1555 = (

let uu____1556 = (FStar_ST.op_Bang c)
in (FStar_Util.string_of_int uu____1556))
in (Prims.strcat x uu____1555));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1721 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1723 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1723) with
| true -> begin
(aux bs e' copt)
end
| uu____1724 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1729 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1729))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1808 -> begin
(

let uu____1809 = (FStar_List.hd l)
in (match (uu____1809) with
| (p1, w1, e1) -> begin
(

let uu____1843 = (

let uu____1852 = (FStar_List.tl l)
in (FStar_List.hd uu____1852))
in (match (uu____1843) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1926 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____1963 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1963) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____1978 -> begin
(

let vs = (FStar_List.map (fun uu____1983 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____1994 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____2008 -> (match (uu____2008) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____1994))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let default_value_for_ty : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g t -> (

let uu____2034 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____2034) with
| (ts, r) -> begin
(

let body = (fun r1 -> (

let r2 = (

let uu____2054 = (FStar_Extraction_ML_Util.udelta_unfold g r1)
in (match (uu____2054) with
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
| uu____2058 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased), (r2)))))
end)))
in (match ((Prims.op_Equality ts [])) with
| true -> begin
(body r)
end
| uu____2061 -> begin
(

let vs = (FStar_List.map (fun uu____2066 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let uu____2074 = (

let uu____2075 = (

let uu____2086 = (body r)
in ((vs_ts), (uu____2086)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____2075))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) uu____2074))))
end))
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____2103 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____2105 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____2105 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))))
in (match (uu____2103) with
| true -> begin
e
end
| uu____2110 -> begin
(eta_expand expect e)
end)))


let maybe_coerce : 'Auu____2123 . 'Auu____2123  ->  FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun pos g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____2150 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____2150) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____2160 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2172 -> (

let uu____2173 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____2174 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____2175 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____2173 uu____2174 uu____2175))))));
(match (ty1) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(default_value_for_ty g expect)
end
| uu____2176 -> begin
(

let uu____2177 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))))
in (maybe_eta_expand expect uu____2177))
end);
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____2188 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____2188) with
| FStar_Util.Inl (uu____2189, t) -> begin
t
end
| uu____2203 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let basic_norm_steps : FStar_TypeChecker_Normalize.step Prims.list = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]


let rec translate_term_to_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let arg_as_mlty = (fun g1 uu____2248 -> (match (uu____2248) with
| (a, uu____2254) -> begin
(

let uu____2255 = (is_type g1 a)
in (match (uu____2255) with
| true -> begin
(translate_term_to_mlty g1 a)
end
| uu____2256 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
in (

let fv_app_as_mlty = (fun g1 fv args -> (

let uu____2273 = (

let uu____2274 = (FStar_Extraction_ML_UEnv.is_fv_type g1 fv)
in (not (uu____2274)))
in (match (uu____2273) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| uu____2275 -> begin
(

let uu____2276 = (

let uu____2289 = (FStar_TypeChecker_Env.lookup_lid g1.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2289) with
| ((uu____2310, fvty), uu____2312) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) g1.FStar_Extraction_ML_UEnv.tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____2276) with
| (formals, uu____2319) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g1) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____2363 = (FStar_Util.first_N n_args formals)
in (match (uu____2363) with
| (uu____2390, rest) -> begin
(

let uu____2416 = (FStar_List.map (fun uu____2424 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____2416))
end))
end
| uu____2429 -> begin
mlargs
end))
in (

let nm = (

let uu____2431 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv)
in (match (uu____2431) with
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
| FStar_Syntax_Syntax.Tm_type (uu____2449) -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2450) -> begin
(

let uu____2451 = (

let uu____2452 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2452))
in (failwith uu____2451))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2453) -> begin
(

let uu____2478 = (

let uu____2479 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2479))
in (failwith uu____2478))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2480 = (

let uu____2481 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2481))
in (failwith uu____2480))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2483 = (FStar_Syntax_Util.unfold_lazy i)
in (translate_term_to_mlty env uu____2483))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2484) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2485) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2492) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____2510) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____2515; FStar_Syntax_Syntax.index = uu____2516; FStar_Syntax_Syntax.sort = t2}, uu____2518) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2526) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2532, uu____2533) -> begin
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

let uu____2600 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2600) with
| (bs1, c1) -> begin
(

let uu____2607 = (binders_as_ml_binders env bs1)
in (match (uu____2607) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2634 = (

let uu____2641 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____2641))
in (match (uu____2634) with
| (ed, qualifiers) -> begin
(

let uu____2662 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____2662) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (translate_term_to_mlty env1 t2)
in res))
end
| uu____2667 -> begin
(translate_term_to_mlty env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2669 = (FStar_List.fold_right (fun uu____2688 uu____2689 -> (match (((uu____2688), (uu____2689))) with
| ((uu____2710, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (uu____2669) with
| (uu____2722, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____2747 = (

let uu____2748 = (FStar_Syntax_Util.un_uinst head1)
in uu____2748.FStar_Syntax_Syntax.n)
in (match (uu____2747) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____2775 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (translate_term_to_mlty env uu____2775))
end
| uu____2792 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2795) -> begin
(

let uu____2816 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____2816) with
| (bs1, ty1) -> begin
(

let uu____2823 = (binders_as_ml_binders env bs1)
in (match (uu____2823) with
| (bts, env1) -> begin
(translate_term_to_mlty env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_let (uu____2848) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____2861) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
in (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____2890) -> begin
(

let uu____2897 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____2897) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____2901 -> begin
false
end))
in (

let uu____2902 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv t0)
in (match (uu____2902) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| uu____2903 -> begin
(

let mlt = (aux g t0)
in (

let uu____2905 = (is_top_ty mlt)
in (match (uu____2905) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::basic_norm_steps) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (aux g t))
end
| uu____2907 -> begin
mlt
end)))
end)))))))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____2920 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2963 b -> (match (uu____2963) with
| (ml_bs, env) -> begin
(

let uu____3003 = (is_type_binder g b)
in (match (uu____3003) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____3021 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____3021), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____3032 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (translate_term_to_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____3035 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____3035) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____3059 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____3059), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____2920) with
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
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____3142) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____3145, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____3149 -> begin
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
| uu____3181 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____3183 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____3184 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____3185 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____3188 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____3209 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____3209) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____3213 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____3240 -> begin
p
end)
end))
end
| uu____3243 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____3335 -> (

let uu____3336 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____3337 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____3336 uu____3337)))))
end
| uu____3338 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, swopt)) when (

let uu____3367 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____3367 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))) -> begin
(

let uu____3372 = (match (swopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3385 = (

let uu____3386 = (

let uu____3387 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (((c), (FStar_Pervasives_Native.None)))))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____3387))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____3386))
in ((uu____3385), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end
| FStar_Pervasives_Native.Some (sw) -> begin
(

let source_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer g.FStar_Extraction_ML_UEnv.tcenv.FStar_TypeChecker_Env.dsenv c sw FStar_Range.dummyRange)
in (

let uu____3408 = (term_as_mlexpr g source_term)
in (match (uu____3408) with
| (mlterm, uu____3420, mlty) -> begin
((mlterm), (mlty))
end)))
end)
in (match (uu____3372) with
| (mlc, ml_ty) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____3440 = (

let uu____3441 = (

let uu____3448 = (

let uu____3451 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ml_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____3451)::(mlc)::[])
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____3448)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3441))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3440))
in (

let uu____3454 = (ok ml_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____3454)))))
end))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____3474 = (

let uu____3483 = (

let uu____3490 = (

let uu____3491 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____3491))
in ((uu____3490), ([])))
in FStar_Pervasives_Native.Some (uu____3483))
in (

let uu____3500 = (ok mlty)
in ((g), (uu____3474), (uu____3500))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3511 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3511) with
| (g1, x1) -> begin
(

let uu____3534 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3557 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3534)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3568 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3568) with
| (g1, x1) -> begin
(

let uu____3591 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3614 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3591)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____3623) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____3662 = (

let uu____3667 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____3667) with
| FStar_Util.Inr (uu____3672, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____3674; FStar_Extraction_ML_Syntax.loc = uu____3675}, ttys, uu____3677) -> begin
((n1), (ttys))
end
| uu____3690 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____3662) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____3712 = (FStar_Util.first_N nTyVars pats)
in (match (uu____3712) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___67_3812 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____3845 -> (match (uu____3845) with
| (p1, uu____3853) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____3858, t) -> begin
(term_as_mlty g t)
end
| uu____3864 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3868 -> (

let uu____3869 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____3869))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____3871 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____3871))))
end)) (fun uu___66_3885 -> (match (uu___66_3885) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____3900 = (FStar_Util.fold_map (fun g1 uu____3936 -> (match (uu____3936) with
| (p1, imp1) -> begin
(

let uu____3955 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None term_as_mlexpr)
in (match (uu____3955) with
| (g2, p2, uu____3984) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____3900) with
| (g1, tyMLPats) -> begin
(

let uu____4045 = (FStar_Util.fold_map (fun uu____4109 uu____4110 -> (match (((uu____4109), (uu____4110))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____4203 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____4263 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____4203) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____4334 = (extract_one_pat false g2 p1 expected_ty term_as_mlexpr)
in (match (uu____4334) with
| (g3, p2, uu____4375) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____4045) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____4493 = (

let uu____4504 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___63_4555 -> (match (uu___63_4555) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____4597 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4504 FStar_List.split))
in (match (uu____4493) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____4670 -> begin
false
end)
in (

let uu____4679 = (

let uu____4688 = (

let uu____4695 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____4698 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____4695), (uu____4698))))
in FStar_Pervasives_Native.Some (uu____4688))
in ((g2), (uu____4679), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t term_as_mlexpr -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____4825 = (extract_one_pat false g1 p1 expected_t1 term_as_mlexpr)
in (match (uu____4825) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____4882 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____4927 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____4927))
end))
in (

let uu____4928 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____4928) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____5078, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____5081 = (

let uu____5092 = (

let uu____5101 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____5101)))
in (uu____5092)::more_args)
in (eta_args uu____5081 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____5114, uu____5115) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____5138 -> begin
(

let uu____5139 = (

let uu____5140 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr)
in (

let uu____5141 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.format2 "Impossible: Head type is not an arrow: (%s : %s)" uu____5140 uu____5141)))
in (failwith uu____5139))
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____5173, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____5205 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____5227 = (eta_args [] residualType)
in (match (uu____5227) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____5280 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____5280))
end
| uu____5281 -> begin
(

let uu____5292 = (FStar_List.unzip eargs)
in (match (uu____5292) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____5334 = (

let uu____5335 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____5335))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____5334))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____5344 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____5347, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5351; FStar_Extraction_ML_Syntax.loc = uu____5352}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____5379 -> begin
(

let uu____5382 = (

let uu____5389 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____5389), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5382))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5393; FStar_Extraction_ML_Syntax.loc = uu____5394}, uu____5395); FStar_Extraction_ML_Syntax.mlty = uu____5396; FStar_Extraction_ML_Syntax.loc = uu____5397}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____5428 -> begin
(

let uu____5431 = (

let uu____5438 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____5438), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5431))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5442; FStar_Extraction_ML_Syntax.loc = uu____5443}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5451 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5451))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5455; FStar_Extraction_ML_Syntax.loc = uu____5456}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5458))) -> begin
(

let uu____5471 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5471))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5475; FStar_Extraction_ML_Syntax.loc = uu____5476}, uu____5477); FStar_Extraction_ML_Syntax.mlty = uu____5478; FStar_Extraction_ML_Syntax.loc = uu____5479}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5491 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5491))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5495; FStar_Extraction_ML_Syntax.loc = uu____5496}, uu____5497); FStar_Extraction_ML_Syntax.mlty = uu____5498; FStar_Extraction_ML_Syntax.loc = uu____5499}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5501))) -> begin
(

let uu____5518 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5518))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5524 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5524))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5528))) -> begin
(

let uu____5537 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5537))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5541; FStar_Extraction_ML_Syntax.loc = uu____5542}, uu____5543), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5550 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5550))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5554; FStar_Extraction_ML_Syntax.loc = uu____5555}, uu____5556), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5557))) -> begin
(

let uu____5570 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5570))
end
| uu____5573 -> begin
mlAppExpr
end)))))


let maybe_promote_effect : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag) = (fun ml_e tag t -> (match (((tag), (t))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| uu____5603 -> begin
((ml_e), (tag))
end))


let rec check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e f ty -> ((FStar_Extraction_ML_UEnv.debug g (fun uu____5668 -> (

let uu____5669 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5670 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.print2 "Checking %s at type %s\n" uu____5669 uu____5670)))));
(match (((f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____5675) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____5676 -> begin
(

let uu____5681 = (term_as_mlexpr g e)
in (match (uu____5681) with
| (ml_e, tag, t) -> begin
(

let uu____5695 = (maybe_promote_effect ml_e tag t)
in (match (uu____5695) with
| (ml_e1, tag1) -> begin
(

let uu____5706 = (FStar_Extraction_ML_Util.eff_leq tag1 f)
in (match (uu____5706) with
| true -> begin
(

let uu____5711 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____5711), (ty)))
end
| uu____5712 -> begin
(match (((tag1), (f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(

let uu____5717 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____5717), (ty)))
end
| uu____5718 -> begin
((err_unexpected_eff g e ty f tag1);
(

let uu____5726 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____5726), (ty)));
)
end)
end))
end))
end))
end);
))
and term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let uu____5729 = (term_as_mlexpr' g e)
in (match (uu____5729) with
| (e1, f, t) -> begin
(

let uu____5745 = (maybe_promote_effect e1 f t)
in (match (uu____5745) with
| (e2, f1) -> begin
((e2), (f1), (t))
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5770 = (

let uu____5771 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5772 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____5773 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____5771 uu____5772 uu____5773))))
in (FStar_Util.print_string uu____5770))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5781 = (

let uu____5782 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5782))
in (failwith uu____5781))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5789) -> begin
(

let uu____5814 = (

let uu____5815 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5815))
in (failwith uu____5814))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5822) -> begin
(

let uu____5839 = (

let uu____5840 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5840))
in (failwith uu____5839))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5847) -> begin
(

let uu____5848 = (

let uu____5849 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5849))
in (failwith uu____5848))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5857 = (FStar_Syntax_Util.unfold_lazy i)
in (term_as_mlexpr g uu____5857))
end
| FStar_Syntax_Syntax.Tm_type (uu____5858) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5859) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5866) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____5880}) -> begin
(

let uu____5895 = (

let uu____5904 = (

let uu____5921 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____5921))
in (FStar_All.pipe_left FStar_Util.right uu____5904))
in (match (uu____5895) with
| (uu____5964, fw, uu____5966, uu____5967) -> begin
(

let uu____5968 = (

let uu____5969 = (

let uu____5970 = (

let uu____5977 = (

let uu____5980 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Open quotation at runtime"))))
in (uu____5980)::[])
in ((fw), (uu____5977)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5970))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____5969))
in ((uu____5968), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) -> begin
(

let uu____5999 = (FStar_Reflection_Basic.inspect_ln qt)
in (match (uu____5999) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____6007 = (FStar_Syntax_Syntax.lookup_aq bv aqs)
in (match (uu____6007) with
| FStar_Pervasives_Native.Some (false, tm) -> begin
(term_as_mlexpr g tm)
end
| FStar_Pervasives_Native.Some (true, tm) -> begin
(

let uu____6030 = (

let uu____6039 = (

let uu____6056 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____6056))
in (FStar_All.pipe_left FStar_Util.right uu____6039))
in (match (uu____6030) with
| (uu____6099, fw, uu____6101, uu____6102) -> begin
(

let uu____6103 = (

let uu____6104 = (

let uu____6105 = (

let uu____6112 = (

let uu____6115 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Open quotation at runtime"))))
in (uu____6115)::[])
in ((fw), (uu____6112)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6105))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____6104))
in ((uu____6103), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let tv = (

let uu____6123 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____6123 t.FStar_Syntax_Syntax.pos (FStar_Reflection_Data.Tv_Var (bv))))
in (

let t1 = (

let uu____6129 = (

let uu____6138 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____6138)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____6129))
in (term_as_mlexpr g t1)))
end))
end
| tv -> begin
(

let tv1 = (

let uu____6141 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____6141 t.FStar_Syntax_Syntax.pos tv))
in (

let t1 = (

let uu____6147 = (

let uu____6156 = (FStar_Syntax_Syntax.as_arg tv1)
in (uu____6156)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____6147))
in (term_as_mlexpr g t1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Error_NoLetMutable), ("let-mutable no longer supported")))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____6170)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____6200 = (

let uu____6207 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____6207))
in (match (uu____6200) with
| (ed, qualifiers) -> begin
(

let uu____6234 = (

let uu____6235 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____6235 Prims.op_Negation))
in (match (uu____6234) with
| true -> begin
(term_as_mlexpr g t2)
end
| uu____6244 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____6251 -> begin
(term_as_mlexpr g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6253) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6259) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____6265 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____6265) with
| (uu____6278, ty, uu____6280) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____6282 = (

let uu____6283 = (FStar_Extraction_ML_Util.mlexpr_of_const t.FStar_Syntax_Syntax.pos c)
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6283))
in ((uu____6282), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____6284) -> begin
(

let uu____6285 = (is_type g t)
in (match (uu____6285) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____6292 -> begin
(

let uu____6293 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____6293) with
| (FStar_Util.Inl (uu____6306), uu____6307) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____6344, x, mltys, uu____6347), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____6393 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____6393), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____6394 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____6402 = (is_type g t)
in (match (uu____6402) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____6409 -> begin
(

let uu____6410 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____6410) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____6419)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (uu____6452, x, mltys, uu____6455)) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____6496 = (maybe_eta_data_and_project_record g fv.FStar_Syntax_Syntax.fv_qual t1 x)
in ((uu____6496), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____6497 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____6527 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____6527) with
| (bs1, body1) -> begin
(

let uu____6540 = (binders_as_ml_binders g bs1)
in (match (uu____6540) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____6573 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____6573) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____6574 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____6578 -> (

let uu____6579 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____6579))));
body1;
)
end)
in (

let uu____6580 = (term_as_mlexpr env body2)
in (match (uu____6580) with
| (ml_body, f, t1) -> begin
(

let uu____6596 = (FStar_List.fold_right (fun uu____6615 uu____6616 -> (match (((uu____6615), (uu____6616))) with
| ((uu____6637, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____6596) with
| (f1, tfun) -> begin
(

let uu____6657 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____6657), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____6664; FStar_Syntax_Syntax.vars = uu____6665}, ((a1, uu____6667))::[]) -> begin
(

let ty = (

let uu____6697 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (term_as_mlty g uu____6697))
in (

let uu____6698 = (

let uu____6699 = (FStar_Extraction_ML_Util.mlexpr_of_range a1.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) uu____6699))
in ((uu____6698), (FStar_Extraction_ML_Syntax.E_PURE), (ty))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____6700; FStar_Syntax_Syntax.vars = uu____6701}, ((t1, uu____6703))::((r, uu____6705))::[]) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6744)); FStar_Syntax_Syntax.pos = uu____6745; FStar_Syntax_Syntax.vars = uu____6746}, uu____6747) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___64_6805 -> (match (uu___64_6805) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6806 -> begin
false
end))))))
in (

let uu____6807 = (

let uu____6812 = (

let uu____6813 = (FStar_Syntax_Subst.compress head1)
in uu____6813.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____6812)))
in (match (uu____6807) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6822), uu____6823) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____6841, FStar_Syntax_Syntax.Tm_abs (bs, uu____6843, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____6864, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____6866 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6866))
in (

let tm = (

let uu____6876 = (

let uu____6881 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____6882 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6881 uu____6882)))
in (uu____6876 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr g tm)))
end
| uu____6891 -> begin
(

let rec extract_app = (fun is_data uu____6944 uu____6945 restArgs -> (match (((uu____6944), (uu____6945))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____7035) -> begin
(

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (

let app = (

let uu____7070 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____7070))
in ((app), (f), (t1))))
end
| (((arg, uu____7074))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____7105 = (

let uu____7110 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____7110), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____7105 rest))
end
| (((e0, uu____7122))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let expected_effect = (

let uu____7155 = ((FStar_Options.lax ()) && (FStar_TypeChecker_Util.short_circuit_head head1))
in (match (uu____7155) with
| true -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| uu____7156 -> begin
FStar_Extraction_ML_Syntax.E_PURE
end))
in (

let uu____7157 = (check_term_as_mlexpr g e0 expected_effect tExpected)
in (match (uu____7157) with
| (e01, tInferred) -> begin
(

let uu____7170 = (

let uu____7175 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::[]))
in ((uu____7175), (t2)))
in (extract_app is_data ((mlhead), ((((e01), (expected_effect)))::mlargs_f)) uu____7170 rest))
end))))
end
| uu____7186 -> begin
(

let uu____7199 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____7199) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(match (t1) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| uu____7221 -> begin
(err_ill_typed_application g top restArgs t1)
end)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____7271 args1 -> (match (uu____7271) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____7303)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7387))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____7389, f', t3)) -> begin
(

let uu____7426 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____7426 t3))
end
| uu____7427 -> begin
((args2), (f1), (t2))
end))
in (

let uu____7452 = (remove_implicits args1 f t1)
in (match (uu____7452) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____7508 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let extract_app_with_instantiations = (fun uu____7532 -> (

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (uu____7540) -> begin
(

let uu____7541 = (

let uu____7554 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7554) with
| (FStar_Util.Inr (uu____7573, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7618 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7541) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7668))::uu____7669 -> begin
(is_type g a)
end
| uu____7688 -> begin
false
end)
in (

let uu____7697 = (match (vars) with
| (uu____7726)::uu____7727 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7738 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7766 = (FStar_Util.first_N n1 args)
in (match (uu____7766) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7855 -> (match (uu____7855) with
| (x, uu____7861) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____7878 -> begin
(

let uu___68_7881 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___68_7881.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___68_7881.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7885) -> begin
(

let uu___69_7886 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___69_7886.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___69_7886.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7887) -> begin
(

let uu___69_7888 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___69_7888.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___69_7888.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7890; FStar_Extraction_ML_Syntax.loc = uu____7891})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___70_7897 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___70_7897.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___70_7897.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7898 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____7907 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7697) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7959 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7959), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7960 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7969) -> begin
(

let uu____7970 = (

let uu____7983 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7983) with
| (FStar_Util.Inr (uu____8002, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____8047 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7970) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____8097))::uu____8098 -> begin
(is_type g a)
end
| uu____8117 -> begin
false
end)
in (

let uu____8126 = (match (vars) with
| (uu____8155)::uu____8156 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____8167 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____8195 = (FStar_Util.first_N n1 args)
in (match (uu____8195) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____8284 -> (match (uu____8284) with
| (x, uu____8290) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____8307 -> begin
(

let uu___68_8310 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___68_8310.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___68_8310.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____8314) -> begin
(

let uu___69_8315 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___69_8315.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___69_8315.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____8316) -> begin
(

let uu___69_8317 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___69_8317.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___69_8317.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____8319; FStar_Extraction_ML_Syntax.loc = uu____8320})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___70_8326 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___70_8326.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___70_8326.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____8327 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____8336 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____8126) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____8388 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____8388), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____8389 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____8398 -> begin
(

let uu____8399 = (term_as_mlexpr g head2)
in (match (uu____8399) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end)))
in (

let uu____8415 = (is_type g t)
in (match (uu____8415) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____8422 -> begin
(

let uu____8423 = (

let uu____8424 = (FStar_Syntax_Util.un_uinst head1)
in uu____8424.FStar_Syntax_Syntax.n)
in (match (uu____8423) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8434 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____8434) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____8443 -> begin
(extract_app_with_instantiations ())
end))
end
| uu____8446 -> begin
(extract_app_with_instantiations ())
end))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____8449), f) -> begin
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

let uu____8516 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____8516) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____8547 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____8560 -> begin
(

let uu____8561 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____8561) with
| true -> begin
((lbs), (e'))
end
| uu____8572 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____8575 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____8575))
in (

let lb1 = (

let uu___71_8577 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___71_8577.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___71_8577.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___71_8577.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___71_8577.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___71_8577.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___71_8577.FStar_Syntax_Syntax.lbpos})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____8547) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____8608 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____8608))
in (

let lbdef = (

let uu____8616 = (FStar_Options.ml_ish ())
in (match (uu____8616) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____8619 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___72_8620 = lb
in {FStar_Syntax_Syntax.lbname = uu___72_8620.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___72_8620.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___72_8620.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___72_8620.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___72_8620.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___72_8620.FStar_Syntax_Syntax.lbpos}))))))
end
| uu____8621 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____8645 -> (match (uu____8645) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____8665; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____8669; FStar_Syntax_Syntax.lbpos = uu____8670} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (

let no_gen = (fun uu____8746 -> (

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e))))
in (

let uu____8808 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.tcenv t2)
in (match (uu____8808) with
| true -> begin
((lbname_), (f_e), (((t2), ((([]), ((([]), (FStar_Extraction_ML_Syntax.MLTY_Erased))))))), (false), (e))
end
| uu____8887 -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____8924 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____8924 (is_type_binder g))) -> begin
(

let uu____8937 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8937) with
| (bs1, c1) -> begin
(

let uu____8962 = (

let uu____8969 = (FStar_Util.prefix_until (fun x -> (

let uu____9005 = (is_type_binder g x)
in (not (uu____9005)))) bs1)
in (match (uu____8969) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____9093 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____9093)))
end))
in (match (uu____8962) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____9138 = (normalize_abs e)
in (FStar_All.pipe_right uu____9138 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____9180 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____9180) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____9233 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____9233) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____9321 uu____9322 -> (match (((uu____9321), (uu____9322))) with
| ((x, uu____9340), (y, uu____9342)) -> begin
(

let uu____9351 = (

let uu____9358 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____9358)))
in FStar_Syntax_Syntax.NT (uu____9351))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____9369 -> (match (uu____9369) with
| (a, uu____9375) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____9384 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____9402 -> (match (uu____9402) with
| (x, uu____9408) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9384), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
((

let uu____9418 = (is_fstar_value body1)
in (not (uu____9418))) || (

let uu____9420 = (FStar_Syntax_Util.is_pure_comp c1)
in (not (uu____9420))))
end
| uu____9421 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____9433 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____9435 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((t2), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____9471 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____9490) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9507 -> (match (uu____9507) with
| (a, uu____9513) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9522 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9534 -> (match (uu____9534) with
| (x, uu____9540) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9522), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9556 -> (match (uu____9556) with
| (bv, uu____9562) -> begin
(

let uu____9563 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9563 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____9605) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9616 -> (match (uu____9616) with
| (a, uu____9622) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9631 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9643 -> (match (uu____9643) with
| (x, uu____9649) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9631), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9665 -> (match (uu____9665) with
| (bv, uu____9671) -> begin
(

let uu____9672 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9672 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____9714) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9725 -> (match (uu____9725) with
| (a, uu____9731) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9740 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9752 -> (match (uu____9752) with
| (x, uu____9758) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9740), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9774 -> (match (uu____9774) with
| (bv, uu____9780) -> begin
(

let uu____9781 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9781 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____9823 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____9842 -> begin
(no_gen ())
end)
end)))))
end))
in (

let check_lb = (fun env uu____9889 -> (match (uu____9889) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____10024 -> (match (uu____10024) with
| (a, uu____10030) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____10032 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____10032) with
| (e1, ty) -> begin
(

let uu____10043 = (maybe_promote_effect e1 f expected_t)
in (match (uu____10043) with
| (e2, f1) -> begin
(

let meta = (match (((f1), (ty))) with
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| uu____10059 -> begin
[]
end)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e2; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = true})))
end))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____10129 = (FStar_List.fold_right (fun lb uu____10220 -> (match (uu____10220) with
| (env, lbs4) -> begin
(

let uu____10345 = lb
in (match (uu____10345) with
| (lbname, uu____10393, (t1, (uu____10395, polytype)), add_unit, uu____10398) -> begin
(

let uu____10411 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____10411) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____10129) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____10613 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____10688 = (term_as_mlexpr env_body e'1)
in (match (uu____10688) with
| (e'2, f', t') -> begin
(

let f = (

let uu____10705 = (

let uu____10708 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____10708)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____10705))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____10716 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____10717 = (

let uu____10718 = (

let uu____10719 = (

let uu____10720 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), (uu____10720)))
in (mk_MLE_Let top_level uu____10719 e'2))
in (

let uu____10729 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____10718 uu____10729)))
in ((uu____10717), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____10768 = (term_as_mlexpr g scrutinee)
in (match (uu____10768) with
| (e, f_e, t_e) -> begin
(

let uu____10784 = (check_pats_for_ite pats)
in (match (uu____10784) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____10845 = (term_as_mlexpr g then_e1)
in (match (uu____10845) with
| (then_mle, f_then, t_then) -> begin
(

let uu____10861 = (term_as_mlexpr g else_e1)
in (match (uu____10861) with
| (else_mle, f_else, t_else) -> begin
(

let uu____10877 = (

let uu____10888 = (type_leq g t_then t_else)
in (match (uu____10888) with
| true -> begin
((t_else), (no_lift))
end
| uu____10905 -> begin
(

let uu____10906 = (type_leq g t_else t_then)
in (match (uu____10906) with
| true -> begin
((t_then), (no_lift))
end
| uu____10923 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____10877) with
| (t_branch, maybe_lift1) -> begin
(

let uu____10950 = (

let uu____10951 = (

let uu____10952 = (

let uu____10961 = (maybe_lift1 then_mle t_then)
in (

let uu____10962 = (

let uu____10965 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____10965))
in ((e), (uu____10961), (uu____10962))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____10952))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____10951))
in (

let uu____10968 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____10950), (uu____10968), (t_branch))))
end))
end))
end))
end
| uu____10969 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____10984 -> begin
(

let uu____10985 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____11094 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____11094) with
| (pat, when_opt, branch1) -> begin
(

let uu____11138 = (extract_pat g pat t_e term_as_mlexpr)
in (match (uu____11138) with
| (env, p, pat_t_compat) -> begin
(

let uu____11196 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let w_pos = w.FStar_Syntax_Syntax.pos
in (

let uu____11219 = (term_as_mlexpr env w)
in (match (uu____11219) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce w_pos env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end)))
end)
in (match (uu____11196) with
| (when_opt1, f_when) -> begin
(

let uu____11268 = (term_as_mlexpr env branch1)
in (match (uu____11268) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____11302 = (FStar_All.pipe_right p (FStar_List.map (fun uu____11379 -> (match (uu____11379) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____11302)))
end))
end))
end))
end))) true))
in (match (uu____10985) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____11539 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____11544 -> (

let uu____11545 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____11546 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____11545 uu____11546)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____11571 = (

let uu____11580 = (

let uu____11597 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____11597))
in (FStar_All.pipe_left FStar_Util.right uu____11580))
in (match (uu____11571) with
| (uu____11640, fw, uu____11642, uu____11643) -> begin
(

let uu____11644 = (

let uu____11645 = (

let uu____11646 = (

let uu____11653 = (

let uu____11656 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____11656)::[])
in ((fw), (uu____11653)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____11646))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____11645))
in ((uu____11644), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| ((uu____11659, uu____11660, (uu____11661, f_first, t_first)))::rest -> begin
(

let uu____11721 = (FStar_List.fold_left (fun uu____11763 uu____11764 -> (match (((uu____11763), (uu____11764))) with
| ((topt, f), (uu____11821, uu____11822, (uu____11823, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____11879 = (type_leq g t1 t_branch)
in (match (uu____11879) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____11882 -> begin
(

let uu____11883 = (type_leq g t_branch t1)
in (match (uu____11883) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____11886 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____11721) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____11978 -> (match (uu____11978) with
| (p, (wopt, uu____12007), (b1, uu____12009, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____12028) -> begin
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

let uu____12033 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____12033), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____12059 = (

let uu____12064 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12064))
in (match (uu____12059) with
| (uu____12089, fstar_disc_type) -> begin
(

let wildcards = (

let uu____12098 = (

let uu____12099 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____12099.FStar_Syntax_Syntax.n)
in (match (uu____12098) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____12109) -> begin
(

let uu____12126 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___65_12158 -> (match (uu___65_12158) with
| (uu____12165, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12166))) -> begin
true
end
| uu____12169 -> begin
false
end))))
in (FStar_All.pipe_right uu____12126 (FStar_List.map (fun uu____12202 -> (

let uu____12209 = (fresh "_")
in ((uu____12209), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____12210 -> begin
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

let uu____12221 = (

let uu____12222 = (

let uu____12233 = (

let uu____12234 = (

let uu____12235 = (

let uu____12250 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____12253 = (

let uu____12264 = (

let uu____12273 = (

let uu____12274 = (

let uu____12281 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____12281), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____12274))
in (

let uu____12284 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____12273), (FStar_Pervasives_Native.None), (uu____12284))))
in (

let uu____12287 = (

let uu____12298 = (

let uu____12307 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____12307)))
in (uu____12298)::[])
in (uu____12264)::uu____12287))
in ((uu____12250), (uu____12253))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____12235))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____12234))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____12233)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____12222))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____12221))
in (

let uu____12362 = (

let uu____12363 = (

let uu____12366 = (

let uu____12367 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____12367; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____12366)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), (uu____12363)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____12362)))))))
end)))




