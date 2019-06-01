
open Prims
open FStar_Pervasives
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____8 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields : 'Auu____77 . FStar_Ident.ident Prims.list  ->  'Auu____77 Prims.list  ->  (Prims.string * 'Auu____77) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail : 'Auu____120 . FStar_Range.range  ->  (FStar_Errors.raw_error * Prims.string)  ->  'Auu____120 = (fun r err -> (FStar_Errors.raise_error err r))


let err_ill_typed_application : 'Auu____156 'Auu____157 . FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  (FStar_Syntax_Syntax.term * 'Auu____156) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____157 = (fun env t mlhead args ty -> (

let uu____195 = (

let uu____201 = (

let uu____203 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____205 = (FStar_Extraction_ML_Code.string_of_mlexpr env.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (

let uu____207 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____209 = (

let uu____211 = (FStar_All.pipe_right args (FStar_List.map (fun uu____232 -> (match (uu____232) with
| (x, uu____239) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____211 (FStar_String.concat " ")))
in (FStar_Util.format4 "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n" uu____203 uu____205 uu____207 uu____209)))))
in ((FStar_Errors.Fatal_IllTyped), (uu____201)))
in (fail t.FStar_Syntax_Syntax.pos uu____195)))


let err_ill_typed_erasure : 'Auu____256 . FStar_Extraction_ML_UEnv.uenv  ->  FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____256 = (fun env pos ty -> (

let uu____272 = (

let uu____278 = (

let uu____280 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format1 "Erased value found where a value of type %s was expected" uu____280))
in ((FStar_Errors.Fatal_IllTyped), (uu____278)))
in (fail pos uu____272)))


let err_value_restriction : 'Auu____289 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____289 = (fun t -> (

let uu____299 = (

let uu____305 = (

let uu____307 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____309 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____307 uu____309)))
in ((FStar_Errors.Fatal_ValueRestriction), (uu____305)))
in (fail t.FStar_Syntax_Syntax.pos uu____299)))


let err_unexpected_eff : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  unit = (fun env t ty f0 f1 -> (

let uu____343 = (

let uu____349 = (

let uu____351 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____353 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____355 = (FStar_Extraction_ML_Util.eff_to_string f0)
in (

let uu____357 = (FStar_Extraction_ML_Util.eff_to_string f1)
in (FStar_Util.format4 "for expression %s of type %s, Expected effect %s; got effect %s" uu____351 uu____353 uu____355 uu____357)))))
in ((FStar_Errors.Warning_ExtractionUnexpectedEffect), (uu____349)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____343)))


let effect_as_etag : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____385 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____385) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____390 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.env_tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____390) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____401, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (

let uu____411 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid)
in (match (uu____411) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____414 -> begin
(

let uu____416 = (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____416) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____419 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.env_tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____442 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____442) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____445 -> begin
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

let uu____466 = (

let uu____467 = (FStar_Syntax_Subst.compress t1)
in uu____467.FStar_Syntax_Syntax.n)
in (match (uu____466) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____473) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____498) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____527) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____537 = (FStar_Syntax_Util.unfold_lazy i)
in (is_arity env uu____537))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____538) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____552) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____554) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____556) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____564) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____566) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____568, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let topt = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env.FStar_Extraction_ML_UEnv.env_tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (topt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____604, t2) -> begin
(is_arity env t2)
end))
end
| FStar_Syntax_Syntax.Tm_app (uu____610) -> begin
(

let uu____627 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____627) with
| (head1, uu____646) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____672) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____678) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____683, body, uu____685) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____710, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____730, branches) -> begin
(match (branches) with
| ((uu____769, uu____770, e))::uu____772 -> begin
(is_arity env e)
end
| uu____819 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____851) -> begin
(

let uu____874 = (

let uu____876 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____876))
in (failwith uu____874))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____880 = (

let uu____882 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____882))
in (failwith uu____880))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____887 = (FStar_Syntax_Util.unfold_lazy i)
in (is_type_aux env uu____887))
end
| FStar_Syntax_Syntax.Tm_constant (uu____888) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____890) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____892) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____900) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uu____919; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____920; FStar_Syntax_Syntax.ctx_uvar_binders = uu____921; FStar_Syntax_Syntax.ctx_uvar_typ = t2; FStar_Syntax_Syntax.ctx_uvar_reason = uu____923; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____924; FStar_Syntax_Syntax.ctx_uvar_range = uu____925; FStar_Syntax_Syntax.ctx_uvar_meta = uu____926}, s) -> begin
(

let uu____975 = (FStar_Syntax_Subst.subst' s t2)
in (is_arity env uu____975))
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____976; FStar_Syntax_Syntax.index = uu____977; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____982; FStar_Syntax_Syntax.index = uu____983; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____989, uu____990) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1032) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1039) -> begin
(

let uu____1064 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____1064) with
| (uu____1070, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1090 = (

let uu____1095 = (

let uu____1096 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1096)::[])
in (FStar_Syntax_Subst.open_term uu____1095 body))
in (match (uu____1090) with
| (uu____1116, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1118, lbs), body) -> begin
(

let uu____1138 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____1138) with
| (uu____1146, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____1152, branches) -> begin
(match (branches) with
| (b)::uu____1192 -> begin
(

let uu____1237 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____1237) with
| (uu____1239, uu____1240, e) -> begin
(is_type_aux env e)
end))
end
| uu____1258 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1276) -> begin
false
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1285) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1291) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1332 -> (

let uu____1333 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1335 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1333 uu____1335)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1344 -> (match (b) with
| true -> begin
(

let uu____1346 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1348 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1346 uu____1348)))
end
| uu____1351 -> begin
(

let uu____1353 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1355 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1353 uu____1355)))
end)));
b;
));
))


let is_type_binder : 'Auu____1365 . FStar_Extraction_ML_UEnv.uenv  ->  (FStar_Syntax_Syntax.bv * 'Auu____1365)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1392 = (

let uu____1393 = (FStar_Syntax_Subst.compress t)
in uu____1393.FStar_Syntax_Syntax.n)
in (match (uu____1392) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1397; FStar_Syntax_Syntax.fv_delta = uu____1398; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1400; FStar_Syntax_Syntax.fv_delta = uu____1401; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1402))}) -> begin
true
end
| uu____1410 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1419 = (

let uu____1420 = (FStar_Syntax_Subst.compress t)
in uu____1420.FStar_Syntax_Syntax.n)
in (match (uu____1419) with
| FStar_Syntax_Syntax.Tm_constant (uu____1424) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1426) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1428) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1430) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1476 = (is_constructor head1)
in (match (uu____1476) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1498 -> (match (uu____1498) with
| (te, uu____1507) -> begin
(is_fstar_value te)
end))))
end
| uu____1512 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1516) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1522, uu____1523) -> begin
(is_fstar_value t1)
end
| uu____1564 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1574) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1576) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1579) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1581) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1594, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1603, fields) -> begin
(FStar_Util.for_all (fun uu____1633 -> (match (uu____1633) with
| (uu____1640, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1645) -> begin
(is_ml_value h)
end
| uu____1650 -> begin
false
end))


let fresh : Prims.string  ->  Prims.string = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1668 = (

let uu____1670 = (FStar_ST.op_Bang c)
in (FStar_Util.string_of_int uu____1670))
in (Prims.op_Hat x uu____1668));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1773 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1775 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1775) with
| true -> begin
(aux bs e' copt)
end
| uu____1780 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1789 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1789))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1878 -> begin
(

let uu____1880 = (FStar_List.hd l)
in (match (uu____1880) with
| (p1, w1, e1) -> begin
(

let uu____1915 = (

let uu____1924 = (FStar_List.tl l)
in (FStar_List.hd uu____1924))
in (match (uu____1915) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____2008 -> begin
def
end)
end))
end))
end)))


let instantiate_tyscheme : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let instantiate_maybe_partial : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun e s tyargs -> (

let uu____2068 = s
in (match (uu____2068) with
| (vars, t) -> begin
(

let n_vars = (FStar_List.length vars)
in (

let n_args = (FStar_List.length tyargs)
in (match ((Prims.op_Equality n_args n_vars)) with
| true -> begin
(match ((Prims.op_Equality n_args (Prims.parse_int "0"))) with
| true -> begin
((e), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| uu____2096 -> begin
(

let ts = (instantiate_tyscheme ((vars), (t)) tyargs)
in (

let tapp = (

let uu___365_2100 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (tyargs))); FStar_Extraction_ML_Syntax.mlty = ts; FStar_Extraction_ML_Syntax.loc = uu___365_2100.FStar_Extraction_ML_Syntax.loc})
in ((tapp), (FStar_Extraction_ML_Syntax.E_PURE), (ts))))
end)
end
| uu____2103 -> begin
(match ((n_args < n_vars)) with
| true -> begin
(

let extra_tyargs = (

let uu____2115 = (FStar_Util.first_N n_args vars)
in (match (uu____2115) with
| (uu____2129, rest_vars) -> begin
(FStar_All.pipe_right rest_vars (FStar_List.map (fun uu____2150 -> FStar_Extraction_ML_Syntax.MLTY_Erased)))
end))
in (

let tyargs1 = (FStar_List.append tyargs extra_tyargs)
in (

let ts = (instantiate_tyscheme ((vars), (t)) tyargs1)
in (

let tapp = (

let uu___376_2157 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (tyargs1))); FStar_Extraction_ML_Syntax.mlty = ts; FStar_Extraction_ML_Syntax.loc = uu___376_2157.FStar_Extraction_ML_Syntax.loc})
in (

let t1 = (FStar_List.fold_left (fun out t1 -> FStar_Extraction_ML_Syntax.MLTY_Fun (((t1), (FStar_Extraction_ML_Syntax.E_PURE), (out)))) ts extra_tyargs)
in (

let f = (

let vs_ts = (FStar_List.map (fun t2 -> (

let uu____2182 = (fresh "t")
in ((uu____2182), (t2)))) extra_tyargs)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (tapp))))))
in ((f), (FStar_Extraction_ML_Syntax.E_PURE), (t1))))))))
end
| uu____2193 -> begin
(failwith "Impossible: instantiate_maybe_partial called with too many arguments")
end)
end)))
end)))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____2213 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____2213) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____2229 -> begin
(

let vs = (FStar_List.map (fun uu____2237 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____2251 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____2268 -> (match (uu____2268) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____2251))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let default_value_for_ty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g t -> (

let uu____2299 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____2299) with
| (ts, r) -> begin
(

let body = (fun r1 -> (

let r2 = (

let uu____2319 = (FStar_Extraction_ML_Util.udelta_unfold g r1)
in (match (uu____2319) with
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
| uu____2323 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased), (r2)))))
end)))
in (match ((Prims.op_Equality ts [])) with
| true -> begin
(body r)
end
| uu____2327 -> begin
(

let vs = (FStar_List.map (fun uu____2335 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let uu____2346 = (

let uu____2347 = (

let uu____2359 = (body r)
in ((vs_ts), (uu____2359)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____2347))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) uu____2346))))
end))
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____2378 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____2381 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____2381 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))))
in (match (uu____2378) with
| true -> begin
e
end
| uu____2387 -> begin
(eta_expand expect e)
end)))


let apply_coercion : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let mk_fun = (fun binder body -> (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (binders, body1) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((binder)::binders), (body1)))
end
| uu____2459 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((binder)::[]), (body)))
end))
in (

let rec aux = (fun e1 ty1 expect1 -> (

let coerce_branch = (fun uu____2514 -> (match (uu____2514) with
| (pat, w, b) -> begin
(

let uu____2538 = (aux b ty1 expect1)
in ((pat), (w), (uu____2538)))
end))
in (match (((e1.FStar_Extraction_ML_Syntax.expr), (ty1), (expect1))) with
| (FStar_Extraction_ML_Syntax.MLE_Fun ((arg)::rest, body), FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2545, t1), FStar_Extraction_ML_Syntax.MLTY_Fun (s0, uu____2548, s1)) -> begin
(

let body1 = (match (rest) with
| [] -> begin
body
end
| uu____2580 -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Fun (((rest), (body)))))
end)
in (

let body2 = (aux body1 t1 s1)
in (

let uu____2596 = (type_leq g s0 t0)
in (match (uu____2596) with
| true -> begin
(FStar_Extraction_ML_Syntax.with_ty expect1 (mk_fun arg body2))
end
| uu____2599 -> begin
(

let lb = (

let uu____2602 = (

let uu____2603 = (

let uu____2604 = (

let uu____2611 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty s0) (FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Pervasives_Native.fst arg))))
in ((uu____2611), (s0), (t0)))
in FStar_Extraction_ML_Syntax.MLE_Coerce (uu____2604))
in (FStar_Extraction_ML_Syntax.with_ty t0 uu____2603))
in {FStar_Extraction_ML_Syntax.mllb_name = (FStar_Pervasives_Native.fst arg); FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (t0))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = uu____2602; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (

let body3 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty s1) (FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((lb)::[]))), (body2)))))
in (FStar_Extraction_ML_Syntax.with_ty expect1 (mk_fun (((FStar_Pervasives_Native.fst arg)), (s0)) body3))))
end))))
end
| (FStar_Extraction_ML_Syntax.MLE_Let (lbs, body), uu____2630, uu____2631) -> begin
(

let uu____2644 = (

let uu____2645 = (

let uu____2656 = (aux body ty1 expect1)
in ((lbs), (uu____2656)))
in FStar_Extraction_ML_Syntax.MLE_Let (uu____2645))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2644))
end
| (FStar_Extraction_ML_Syntax.MLE_Match (s, branches), uu____2665, uu____2666) -> begin
(

let uu____2687 = (

let uu____2688 = (

let uu____2703 = (FStar_List.map coerce_branch branches)
in ((s), (uu____2703)))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____2688))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2687))
end
| (FStar_Extraction_ML_Syntax.MLE_If (s, b1, b2_opt), uu____2743, uu____2744) -> begin
(

let uu____2749 = (

let uu____2750 = (

let uu____2759 = (aux b1 ty1 expect1)
in (

let uu____2760 = (FStar_Util.map_opt b2_opt (fun b2 -> (aux b2 ty1 expect1)))
in ((s), (uu____2759), (uu____2760))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____2750))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2749))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es), uu____2768, uu____2769) -> begin
(

let uu____2772 = (FStar_Util.prefix es)
in (match (uu____2772) with
| (prefix1, last1) -> begin
(

let uu____2785 = (

let uu____2786 = (

let uu____2789 = (

let uu____2792 = (aux last1 ty1 expect1)
in (uu____2792)::[])
in (FStar_List.append prefix1 uu____2789))
in FStar_Extraction_ML_Syntax.MLE_Seq (uu____2786))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2785))
end))
end
| (FStar_Extraction_ML_Syntax.MLE_Try (s, branches), uu____2795, uu____2796) -> begin
(

let uu____2817 = (

let uu____2818 = (

let uu____2833 = (FStar_List.map coerce_branch branches)
in ((s), (uu____2833)))
in FStar_Extraction_ML_Syntax.MLE_Try (uu____2818))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2817))
end
| uu____2870 -> begin
(FStar_Extraction_ML_Syntax.with_ty expect1 (FStar_Extraction_ML_Syntax.MLE_Coerce (((e1), (ty1), (expect1)))))
end)))
in (aux e ty expect))))


let maybe_coerce : 'Auu____2890 . 'Auu____2890  ->  FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun pos g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____2917 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____2917) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____2930 -> begin
(match (ty1) with
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(default_value_for_ty g expect)
end
| uu____2938 -> begin
(

let uu____2939 = (

let uu____2941 = (FStar_Extraction_ML_Util.erase_effect_annotations ty1)
in (

let uu____2942 = (FStar_Extraction_ML_Util.erase_effect_annotations expect)
in (type_leq g uu____2941 uu____2942)))
in (match (uu____2939) with
| true -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2948 -> (

let uu____2949 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____2951 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (FStar_Util.print2 "\n Effect mismatch on type of %s : %s\n" uu____2949 uu____2951)))));
e;
)
end
| uu____2954 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2961 -> (

let uu____2962 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____2964 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____2966 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____2962 uu____2964 uu____2966))))));
(

let uu____2969 = (apply_coercion g e ty1 expect)
in (maybe_eta_expand expect uu____2969));
)
end))
end)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____2981 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____2981) with
| FStar_Util.Inl (ty_b) -> begin
ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
end
| uu____2983 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let extraction_norm_steps : FStar_TypeChecker_Env.step Prims.list = (FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.ForExtraction)::[]


let comp_no_args : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____3001) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____3010) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let effect_args = (FStar_List.map (fun uu____3046 -> (match (uu____3046) with
| (uu____3061, aq) -> begin
((FStar_Syntax_Syntax.t_unit), (aq))
end)) ct.FStar_Syntax_Syntax.effect_args)
in (

let ct1 = (

let uu___538_3074 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___538_3074.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___538_3074.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___538_3074.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = uu___538_3074.FStar_Syntax_Syntax.flags})
in (

let c1 = (

let uu___541_3078 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___541_3078.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___541_3078.FStar_Syntax_Syntax.vars})
in c1)))
end))


let rec translate_term_to_mlty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let arg_as_mlty = (fun g1 uu____3127 -> (match (uu____3127) with
| (a, uu____3135) -> begin
(

let uu____3140 = (is_type g1 a)
in (match (uu____3140) with
| true -> begin
(translate_term_to_mlty g1 a)
end
| uu____3143 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
in (

let fv_app_as_mlty = (fun g1 fv args -> (

let uu____3161 = (

let uu____3163 = (FStar_Extraction_ML_UEnv.is_fv_type g1 fv)
in (not (uu____3163)))
in (match (uu____3161) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| uu____3166 -> begin
(

let uu____3168 = (

let uu____3183 = (FStar_TypeChecker_Env.lookup_lid g1.FStar_Extraction_ML_UEnv.env_tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3183) with
| ((uu____3206, fvty), uu____3208) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) g1.FStar_Extraction_ML_UEnv.env_tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____3168) with
| (formals, uu____3215) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g1) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____3268 = (FStar_Util.first_N n_args formals)
in (match (uu____3268) with
| (uu____3297, rest) -> begin
(

let uu____3331 = (FStar_List.map (fun uu____3341 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____3331))
end))
end
| uu____3348 -> begin
mlargs
end))
in (

let nm = (

let uu____3351 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv)
in (match (uu____3351) with
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
| FStar_Syntax_Syntax.Tm_type (uu____3369) -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3370) -> begin
(

let uu____3371 = (

let uu____3373 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____3373))
in (failwith uu____3371))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3376) -> begin
(

let uu____3399 = (

let uu____3401 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____3401))
in (failwith uu____3399))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3404 = (

let uu____3406 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____3406))
in (failwith uu____3404))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____3410 = (FStar_Syntax_Util.unfold_lazy i)
in (translate_term_to_mlty env uu____3410))
end
| FStar_Syntax_Syntax.Tm_constant (uu____3411) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_quoted (uu____3412) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3419) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____3433) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____3438; FStar_Syntax_Syntax.index = uu____3439; FStar_Syntax_Syntax.sort = t2}, uu____3441) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____3450) -> begin
(translate_term_to_mlty env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3456, uu____3457) -> begin
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

let uu____3530 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3530) with
| (bs1, c1) -> begin
(

let uu____3537 = (binders_as_ml_binders env bs1)
in (match (uu____3537) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.env_tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let c2 = (comp_no_args c1)
in (

let uu____3570 = (

let uu____3577 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.env_tcenv eff)
in (FStar_Util.must uu____3577))
in (match (uu____3570) with
| (ed, qualifiers) -> begin
(

let uu____3598 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname)
in (match (uu____3598) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.env_tcenv c2 FStar_Syntax_Syntax.U_unknown)
in ((FStar_Extraction_ML_UEnv.debug env1 (fun uu____3606 -> (

let uu____3607 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____3609 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Translating comp type %s as %s\n" uu____3607 uu____3609)))));
(

let res = (translate_term_to_mlty env1 t2)
in ((FStar_Extraction_ML_UEnv.debug env1 (fun uu____3618 -> (

let uu____3619 = (FStar_Syntax_Print.comp_to_string c2)
in (

let uu____3621 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____3623 = (FStar_Extraction_ML_Code.string_of_mlty env1.FStar_Extraction_ML_UEnv.currentModule res)
in (FStar_Util.print3 "Translated comp type %s as %s ... to %s\n" uu____3619 uu____3621 uu____3623))))));
res;
));
))
end
| uu____3626 -> begin
(translate_term_to_mlty env1 (FStar_Syntax_Util.comp_result c2))
end))
end))))
in (

let erase = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____3629 = (FStar_List.fold_right (fun uu____3649 uu____3650 -> (match (((uu____3649), (uu____3650))) with
| ((uu____3673, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (uu____3629) with
| (uu____3688, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____3717 = (

let uu____3718 = (FStar_Syntax_Util.un_uinst head1)
in uu____3718.FStar_Syntax_Syntax.n)
in (match (uu____3717) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____3749 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (translate_term_to_mlty env uu____3749))
end
| uu____3770 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____3773) -> begin
(

let uu____3798 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____3798) with
| (bs1, ty1) -> begin
(

let uu____3805 = (binders_as_ml_binders env bs1)
in (match (uu____3805) with
| (bts, env1) -> begin
(translate_term_to_mlty env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_let (uu____3833) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____3847) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
in (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____3879) -> begin
(

let uu____3886 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____3886) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____3892 -> begin
false
end))
in (

let uu____3894 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv t0)
in (match (uu____3894) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Erased
end
| uu____3897 -> begin
(

let mlt = (aux g t0)
in (

let uu____3900 = (is_top_ty mlt)
in (match (uu____3900) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| uu____3903 -> begin
mlt
end)))
end)))))))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.uenv) = (fun g bs -> (

let uu____3918 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____3974 b -> (match (uu____3974) with
| (ml_bs, env) -> begin
(

let uu____4020 = (is_type_binder g b)
in (match (uu____4020) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____4046 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____4046), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____4061 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (translate_term_to_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____4067 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____4067) with
| (env1, b2, uu____4092) -> begin
(

let ml_b = (

let uu____4101 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____4101), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____3918) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let term_as_mlty : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize extraction_norm_steps g.FStar_Extraction_ML_UEnv.env_tcenv t0)
in (translate_term_to_mlty g t)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____4197) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____4200, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____4204 -> begin
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
| uu____4233 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____4238 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____4239 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____4240 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____4249 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____4277 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____4277) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____4284 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____4317 -> begin
p
end)
end))
end
| uu____4320 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____4422 -> (

let uu____4423 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____4425 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____4423 uu____4425)))))
end
| uu____4428 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, swopt)) when (

let uu____4461 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____4461 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))) -> begin
(

let uu____4466 = (match (swopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4479 = (

let uu____4480 = (

let uu____4481 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (((c), (FStar_Pervasives_Native.None)))))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4481))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____4480))
in ((uu____4479), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end
| FStar_Pervasives_Native.Some (sw) -> begin
(

let source_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer g.FStar_Extraction_ML_UEnv.env_tcenv.FStar_TypeChecker_Env.dsenv c sw FStar_Range.dummyRange)
in (

let uu____4503 = (term_as_mlexpr g source_term)
in (match (uu____4503) with
| (mlterm, uu____4515, mlty) -> begin
((mlterm), (mlty))
end)))
end)
in (match (uu____4466) with
| (mlc, ml_ty) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____4537 = (

let uu____4538 = (

let uu____4545 = (

let uu____4548 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ml_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____4548)::(mlc)::[])
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____4545)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4538))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____4537))
in (

let uu____4551 = (ok ml_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____4551)))))
end))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant g.FStar_Extraction_ML_UEnv.env_tcenv FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____4573 = (

let uu____4582 = (

let uu____4589 = (

let uu____4590 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____4590))
in ((uu____4589), ([])))
in FStar_Pervasives_Native.Some (uu____4582))
in (

let uu____4599 = (ok mlty)
in ((g), (uu____4573), (uu____4599))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____4612 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____4612) with
| (g1, x1, uu____4640) -> begin
(

let uu____4643 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4669 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____4643)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____4681 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____4681) with
| (g1, x1, uu____4709) -> begin
(

let uu____4712 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4738 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____4712)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____4748) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____4791 = (

let uu____4800 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____4800) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____4809; FStar_Extraction_ML_UEnv.exp_b_expr = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____4811; FStar_Extraction_ML_Syntax.loc = uu____4812}; FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____4814} -> begin
((n1), (ttys))
end
| uu____4821 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____4791) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____4858 = (FStar_Util.first_N nTyVars pats)
in (match (uu____4858) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___836_4962 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____4993 -> (match (uu____4993) with
| (p1, uu____5000) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____5003, t) -> begin
(term_as_mlty g t)
end
| uu____5009 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____5013 -> (

let uu____5014 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____5014))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____5018 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____5018))))
end)) (fun uu___835_5032 -> (match (uu___835_5032) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____5047 = (FStar_Util.fold_map (fun g1 uu____5084 -> (match (uu____5084) with
| (p1, imp1) -> begin
(

let uu____5106 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None term_as_mlexpr)
in (match (uu____5106) with
| (g2, p2, uu____5137) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____5047) with
| (g1, tyMLPats) -> begin
(

let uu____5201 = (FStar_Util.fold_map (fun uu____5266 uu____5267 -> (match (((uu____5266), (uu____5267))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____5365 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____5425 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____5365) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____5496 = (extract_one_pat false g2 p1 expected_ty term_as_mlexpr)
in (match (uu____5496) with
| (g3, p2, uu____5539) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____5201) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____5660 = (

let uu____5671 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___0_5722 -> (match (uu___0_5722) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____5764 -> begin
[]
end))))
in (FStar_All.pipe_right uu____5671 FStar_List.split))
in (match (uu____5660) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____5840 -> begin
false
end)
in (

let uu____5850 = (

let uu____5859 = (

let uu____5866 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____5869 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____5866), (uu____5869))))
in FStar_Pervasives_Native.Some (uu____5859))
in ((g2), (uu____5850), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.uenv * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t term_as_mlexpr -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____6001 = (extract_one_pat false g1 p1 expected_t1 term_as_mlexpr)
in (match (uu____6001) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____6064 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____6112 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____6112))
end))
in (

let uu____6113 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____6113) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____6273, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____6277 = (

let uu____6289 = (

let uu____6299 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____6299)))
in (uu____6289)::more_args)
in (eta_args uu____6277 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____6315, uu____6316) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____6341 -> begin
(

let uu____6342 = (

let uu____6344 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr)
in (

let uu____6346 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.format2 "Impossible: Head type is not an arrow: (%s : %s)" uu____6344 uu____6346)))
in (failwith uu____6342))
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____6381, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____6418 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____6440 = (eta_args [] residualType)
in (match (uu____6440) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____6498 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____6498))
end
| uu____6499 -> begin
(

let uu____6511 = (FStar_List.unzip eargs)
in (match (uu____6511) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____6557 = (

let uu____6558 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____6558))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____6557))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____6568 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____6572, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6576; FStar_Extraction_ML_Syntax.loc = uu____6577}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____6600 -> begin
(

let uu____6603 = (

let uu____6610 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____6610), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6603))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6614; FStar_Extraction_ML_Syntax.loc = uu____6615}, uu____6616); FStar_Extraction_ML_Syntax.mlty = uu____6617; FStar_Extraction_ML_Syntax.loc = uu____6618}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____6645 -> begin
(

let uu____6648 = (

let uu____6655 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____6655), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6648))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6659; FStar_Extraction_ML_Syntax.loc = uu____6660}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6668 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6668))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6672; FStar_Extraction_ML_Syntax.loc = uu____6673}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6675))) -> begin
(

let uu____6688 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6688))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6692; FStar_Extraction_ML_Syntax.loc = uu____6693}, uu____6694); FStar_Extraction_ML_Syntax.mlty = uu____6695; FStar_Extraction_ML_Syntax.loc = uu____6696}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6708 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6708))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6712; FStar_Extraction_ML_Syntax.loc = uu____6713}, uu____6714); FStar_Extraction_ML_Syntax.mlty = uu____6715; FStar_Extraction_ML_Syntax.loc = uu____6716}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6718))) -> begin
(

let uu____6735 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6735))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6741 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6741))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6745))) -> begin
(

let uu____6754 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6754))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6758; FStar_Extraction_ML_Syntax.loc = uu____6759}, uu____6760), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____6767 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6767))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____6771; FStar_Extraction_ML_Syntax.loc = uu____6772}, uu____6773), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____6774))) -> begin
(

let uu____6787 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6787))
end
| uu____6790 -> begin
mlAppExpr
end)))))


let maybe_promote_effect : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag) = (fun ml_e tag t -> (match (((tag), (t))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE))
end
| uu____6821 -> begin
((ml_e), (tag))
end))


let extract_lb_sig : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.letbindings  ->  (FStar_Syntax_Syntax.lbname * FStar_Extraction_ML_Syntax.e_tag * (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.binders * FStar_Extraction_ML_Syntax.mltyscheme)) * Prims.bool * FStar_Syntax_Syntax.term) Prims.list = (fun g lbs -> (

let maybe_generalize = (fun uu____6882 -> (match (uu____6882) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____6903; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu____6907; FStar_Syntax_Syntax.lbpos = uu____6908} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let lbtyp1 = (FStar_Syntax_Subst.compress lbtyp)
in (

let no_gen = (fun uu____6989 -> (

let expected_t = (term_as_mlty g lbtyp1)
in ((lbname_), (f_e), (((lbtyp1), ((([]), ((([]), (expected_t))))))), (false), (lbdef))))
in (

let uu____7066 = (FStar_TypeChecker_Util.must_erase_for_extraction g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1)
in (match (uu____7066) with
| true -> begin
((lbname_), (f_e), (((lbtyp1), ((([]), ((([]), (FStar_Extraction_ML_Syntax.MLTY_Erased))))))), (false), (lbdef))
end
| uu____7109 -> begin
(match (lbtyp1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____7152 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____7152 (is_type_binder g))) -> begin
(

let uu____7174 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7174) with
| (bs1, c1) -> begin
(

let uu____7200 = (

let uu____7213 = (FStar_Util.prefix_until (fun x -> (

let uu____7259 = (is_type_binder g x)
in (not (uu____7259)))) bs1)
in (match (uu____7213) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____7386 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____7386)))
end))
in (match (uu____7200) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let lbdef1 = (

let uu____7448 = (normalize_abs lbdef)
in (FStar_All.pipe_right uu____7448 FStar_Syntax_Util.unmeta))
in (match (lbdef1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____7497 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____7497) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____7549 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____7549) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____7652 uu____7653 -> (match (((uu____7652), (uu____7653))) with
| ((x, uu____7679), (y, uu____7681)) -> begin
(

let uu____7702 = (

let uu____7709 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____7709)))
in FStar_Syntax_Syntax.NT (uu____7702))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____7726 -> (match (uu____7726) with
| (a, uu____7734) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____7745 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____7764 -> (match (uu____7764) with
| (x, uu____7773) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____7745), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
((

let uu____7789 = (is_fstar_value body1)
in (not (uu____7789))) || (

let uu____7792 = (FStar_Syntax_Util.is_pure_comp c1)
in (not (uu____7792))))
end
| uu____7794 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____7812 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____7816 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((lbtyp1), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____7834 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____7856) -> begin
(

let env = (FStar_List.fold_left (fun env uu____7875 -> (match (uu____7875) with
| (a, uu____7883) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____7894 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____7913 -> (match (uu____7913) with
| (x, uu____7922) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____7894), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____7966 -> (match (uu____7966) with
| (bv, uu____7974) -> begin
(

let uu____7979 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____7979 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8009) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8022 -> (match (uu____8022) with
| (a, uu____8030) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8041 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8060 -> (match (uu____8060) with
| (x, uu____8069) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8041), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8113 -> (match (uu____8113) with
| (bv, uu____8121) -> begin
(

let uu____8126 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8126 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____8156) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8169 -> (match (uu____8169) with
| (a, uu____8177) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8188 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8207 -> (match (uu____8207) with
| (x, uu____8216) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8188), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8260 -> (match (uu____8260) with
| (bv, uu____8268) -> begin
(

let uu____8273 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8273 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((lbdef1), (args)))) FStar_Pervasives_Native.None lbdef1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((lbtyp1), (((tbinders), (polytype))))), (false), (e)))))))
end
| uu____8303 -> begin
(err_value_restriction lbdef1)
end)))
end))
end))
end
| uu____8323 -> begin
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
in (FStar_Util.fold_map (fun env uu____8474 -> (match (uu____8474) with
| (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body) -> begin
(

let uu____8535 = (FStar_Extraction_ML_UEnv.extend_lb env lbname typ mltyscheme add_unit is_rec)
in (match (uu____8535) with
| (env1, uu____8552, exp_binding) -> begin
(

let uu____8556 = (

let uu____8561 = (FStar_Util.right lbname)
in ((uu____8561), (exp_binding)))
in ((env1), (uu____8556)))
end))
end)) g lbs1)))))


let rec check_term_as_mlexpr : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e f ty -> ((FStar_Extraction_ML_UEnv.debug g (fun uu____8627 -> (

let uu____8628 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____8630 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.print2 "Checking %s at type %s\n" uu____8628 uu____8630)))));
(match (((f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, uu____8637) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____8638 -> begin
(

let uu____8643 = (term_as_mlexpr g e)
in (match (uu____8643) with
| (ml_e, tag, t) -> begin
(

let uu____8657 = (maybe_promote_effect ml_e tag t)
in (match (uu____8657) with
| (ml_e1, tag1) -> begin
(

let uu____8668 = (FStar_Extraction_ML_Util.eff_leq tag1 f)
in (match (uu____8668) with
| true -> begin
(

let uu____8675 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____8675), (ty)))
end
| uu____8676 -> begin
(match (((tag1), (f), (ty))) with
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(

let uu____8682 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____8682), (ty)))
end
| uu____8683 -> begin
((err_unexpected_eff g e ty f tag1);
(

let uu____8691 = (maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t ty)
in ((uu____8691), (ty)));
)
end)
end))
end))
end))
end);
))
and term_as_mlexpr : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e -> (

let uu____8694 = (term_as_mlexpr' g e)
in (match (uu____8694) with
| (e1, f, t) -> begin
(

let uu____8710 = (maybe_promote_effect e1 f t)
in (match (uu____8710) with
| (e2, f1) -> begin
((e2), (f1), (t))
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____8735 = (

let uu____8737 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____8739 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____8741 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____8737 uu____8739 uu____8741))))
in (FStar_Util.print_string uu____8735))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____8751 = (

let uu____8753 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8753))
in (failwith uu____8751))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____8762) -> begin
(

let uu____8785 = (

let uu____8787 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8787))
in (failwith uu____8785))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____8796) -> begin
(

let uu____8809 = (

let uu____8811 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8811))
in (failwith uu____8809))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____8820) -> begin
(

let uu____8821 = (

let uu____8823 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8823))
in (failwith uu____8821))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____8833 = (FStar_Syntax_Util.unfold_lazy i)
in (term_as_mlexpr g uu____8833))
end
| FStar_Syntax_Syntax.Tm_type (uu____8834) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____8835) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____8842) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____8858}) -> begin
(

let uu____8871 = (

let uu____8872 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____8872))
in (match (uu____8871) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____8879; FStar_Extraction_ML_UEnv.exp_b_expr = fw; FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____8881; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____8882} -> begin
(

let uu____8885 = (

let uu____8886 = (

let uu____8887 = (

let uu____8894 = (

let uu____8897 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Cannot evaluate open quotation at runtime"))))
in (uu____8897)::[])
in ((fw), (uu____8894)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____8887))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____8886))
in ((uu____8885), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) -> begin
(

let uu____8915 = (FStar_Reflection_Basic.inspect_ln qt)
in (match (uu____8915) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____8923 = (FStar_Syntax_Syntax.lookup_aq bv aqs)
in (match (uu____8923) with
| FStar_Pervasives_Native.Some (tm) -> begin
(term_as_mlexpr g tm)
end
| FStar_Pervasives_Native.None -> begin
(

let tv = (

let uu____8934 = (

let uu____8941 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____8941 (FStar_Reflection_Data.Tv_Var (bv))))
in (uu____8934 t.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in (

let t1 = (

let uu____8949 = (

let uu____8960 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____8960)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____8949))
in (term_as_mlexpr g t1)))
end))
end
| tv -> begin
(

let tv1 = (

let uu____8987 = (

let uu____8994 = (FStar_Reflection_Embeddings.e_term_view_aq aqs)
in (FStar_Syntax_Embeddings.embed uu____8994 tv))
in (uu____8987 t.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in (

let t1 = (

let uu____9002 = (

let uu____9013 = (FStar_Syntax_Syntax.as_arg tv1)
in (uu____9013)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____9002))
in (term_as_mlexpr g t1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____9040)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____9073 = (

let uu____9080 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.env_tcenv m)
in (FStar_Util.must uu____9080))
in (match (uu____9073) with
| (ed, qualifiers) -> begin
(

let uu____9107 = (

let uu____9109 = (FStar_TypeChecker_Env.is_reifiable_effect g.FStar_Extraction_ML_UEnv.env_tcenv ed.FStar_Syntax_Syntax.mname)
in (not (uu____9109)))
in (match (uu____9107) with
| true -> begin
(term_as_mlexpr g t2)
end
| uu____9118 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____9127 -> begin
(term_as_mlexpr g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____9129) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____9135) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____9141 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (match (uu____9141) with
| (uu____9154, ty, uu____9156) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____9158 = (

let uu____9159 = (FStar_Extraction_ML_Util.mlexpr_of_const t.FStar_Syntax_Syntax.pos c)
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9159))
in ((uu____9158), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____9160) -> begin
(

let uu____9161 = (is_type g t)
in (match (uu____9161) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____9170 -> begin
(

let uu____9172 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____9172) with
| (FStar_Util.Inl (uu____9185), uu____9186) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr ({FStar_Extraction_ML_UEnv.exp_b_name = uu____9191; FStar_Extraction_ML_UEnv.exp_b_expr = x; FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9194}), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____9212 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____9212), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____9213 -> begin
(instantiate_maybe_partial x mltys [])
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____9215 = (is_type g t)
in (match (uu____9215) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____9224 -> begin
(

let uu____9226 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____9226) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_UEnv.exp_b_name = uu____9235; FStar_Extraction_ML_UEnv.exp_b_expr = x; FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9238}) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____9246 -> (

let uu____9247 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____9249 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule x)
in (

let uu____9251 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule (FStar_Pervasives_Native.snd mltys))
in (FStar_Util.print3 "looked up %s: got %s at %s \n" uu____9247 uu____9249 uu____9251))))));
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____9264 = (maybe_eta_data_and_project_record g fv.FStar_Syntax_Syntax.fv_qual t1 x)
in ((uu____9264), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____9265 -> begin
(instantiate_maybe_partial x mltys [])
end);
)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, rcopt) -> begin
(

let uu____9293 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____9293) with
| (bs1, body1) -> begin
(

let uu____9306 = (binders_as_ml_binders g bs1)
in (match (uu____9306) with
| (ml_bs, env) -> begin
(

let body2 = (match (rcopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____9342 = (FStar_TypeChecker_Env.is_reifiable_rc env.FStar_Extraction_ML_UEnv.env_tcenv rc)
in (match (uu____9342) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.env_tcenv body1)
end
| uu____9345 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____9350 -> (

let uu____9351 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____9351))));
body1;
)
end)
in (

let uu____9354 = (term_as_mlexpr env body2)
in (match (uu____9354) with
| (ml_body, f, t1) -> begin
(

let uu____9370 = (FStar_List.fold_right (fun uu____9390 uu____9391 -> (match (((uu____9390), (uu____9391))) with
| ((uu____9414, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____9370) with
| (f1, tfun) -> begin
(

let uu____9437 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____9437), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____9445; FStar_Syntax_Syntax.vars = uu____9446}, ((a1, uu____9448))::[]) -> begin
(

let ty = (

let uu____9488 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (term_as_mlty g uu____9488))
in (

let uu____9489 = (

let uu____9490 = (FStar_Extraction_ML_Util.mlexpr_of_range a1.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) uu____9490))
in ((uu____9489), (FStar_Extraction_ML_Syntax.E_PURE), (ty))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____9491; FStar_Syntax_Syntax.vars = uu____9492}, ((t1, uu____9494))::((r, uu____9496))::[]) -> begin
(term_as_mlexpr g t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____9551)); FStar_Syntax_Syntax.pos = uu____9552; FStar_Syntax_Syntax.vars = uu____9553}, uu____9554) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___1_9623 -> (match (uu___1_9623) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____9626 -> begin
false
end))))))
in (

let uu____9628 = (

let uu____9633 = (

let uu____9634 = (FStar_Syntax_Subst.compress head1)
in uu____9634.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____9633)))
in (match (uu____9628) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____9643), uu____9644) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____9658, FStar_Syntax_Syntax.Tm_abs (bs, uu____9660, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.env_tcenv t)
in (term_as_mlexpr g t1))
end
| (uu____9685, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____9687 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____9687))
in (

let tm = (

let uu____9699 = (

let uu____9704 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____9705 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____9704 uu____9705)))
in (uu____9699 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr g tm)))
end
| uu____9714 -> begin
(

let rec extract_app = (fun is_data uu____9767 uu____9768 restArgs -> (match (((uu____9767), (uu____9768))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(

let mk_head = (fun uu____9849 -> (

let mlargs = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____9876 -> (

let uu____9877 = (

let uu____9879 = (mk_head ())
in (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule uu____9879))
in (

let uu____9880 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t1)
in (

let uu____9882 = (match (restArgs) with
| [] -> begin
"none"
end
| ((hd1, uu____9893))::uu____9894 -> begin
(FStar_Syntax_Print.term_to_string hd1)
end)
in (FStar_Util.print3 "extract_app ml_head=%s type of head = %s, next arg = %s\n" uu____9877 uu____9880 uu____9882))))));
(match (((restArgs), (t1))) with
| ([], uu____9928) -> begin
(

let app = (

let uu____9944 = (mk_head ())
in (maybe_eta_data_and_project_record g is_data t1 uu____9944))
in ((app), (f), (t1)))
end
| (((arg, uu____9946))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____9977 = (

let uu____9982 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____9982), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____9977 rest))
end
| (((e0, uu____9994))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let expected_effect = (

let uu____10027 = ((FStar_Options.lax ()) && (FStar_TypeChecker_Util.short_circuit_head head1))
in (match (uu____10027) with
| true -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| uu____10030 -> begin
FStar_Extraction_ML_Syntax.E_PURE
end))
in (

let uu____10032 = (check_term_as_mlexpr g e0 expected_effect tExpected)
in (match (uu____10032) with
| (e01, tInferred) -> begin
(

let uu____10045 = (

let uu____10050 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::[]))
in ((uu____10050), (t2)))
in (extract_app is_data ((mlhead), ((((e01), (expected_effect)))::mlargs_f)) uu____10045 rest))
end))))
end
| uu____10061 -> begin
(

let uu____10074 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____10074) with
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
| uu____10146 -> begin
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

let extract_app_maybe_projector = (fun is_data mlhead uu____10217 args1 -> (match (uu____10217) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____10247)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10331))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____10333, f', t3)) -> begin
(

let uu____10371 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____10371 t3))
end
| uu____10372 -> begin
((args2), (f1), (t2))
end))
in (

let uu____10397 = (remove_implicits args1 f t1)
in (match (uu____10397) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____10453 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let extract_app_with_instantiations = (fun uu____10477 -> (

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (uu____10485) -> begin
(

let uu____10486 = (

let uu____10507 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____10507) with
| (FStar_Util.Inr (exp_b), q) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____10546 -> (

let uu____10547 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____10549 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule exp_b.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____10551 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule (FStar_Pervasives_Native.snd exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme))
in (

let uu____10553 = (FStar_Util.string_of_bool exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.print4 "@@@looked up %s: got %s at %s (inst_ok=%s)\n" uu____10547 uu____10549 uu____10551 uu____10553)))))));
((((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr), (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme), (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok))), (q));
)
end
| uu____10580 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____10486) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____10656))::uu____10657 -> begin
(is_type g a)
end
| uu____10684 -> begin
false
end)
in (

let uu____10696 = (match (vars) with
| (uu____10725)::uu____10726 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____10740 -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____10746 = (match (((FStar_List.length args) <= n1)) with
| true -> begin
(

let uu____10784 = (FStar_List.map (fun uu____10796 -> (match (uu____10796) with
| (x, uu____10804) -> begin
(term_as_mlty g x)
end)) args)
in ((uu____10784), ([])))
end
| uu____10825 -> begin
(

let uu____10827 = (FStar_Util.first_N n1 args)
in (match (uu____10827) with
| (prefix1, rest) -> begin
(

let uu____10916 = (FStar_List.map (fun uu____10928 -> (match (uu____10928) with
| (x, uu____10936) -> begin
(term_as_mlty g x)
end)) prefix1)
in ((uu____10916), (rest)))
end))
end)
in (match (uu____10746) with
| (provided_type_args, rest) -> begin
(

let uu____10987 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____10996) -> begin
(

let uu____10997 = (instantiate_maybe_partial head_ml ((vars), (t1)) provided_type_args)
in (match (uu____10997) with
| (head3, uu____11009, t2) -> begin
((head3), (t2))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____11011) -> begin
(

let uu____11013 = (instantiate_maybe_partial head_ml ((vars), (t1)) provided_type_args)
in (match (uu____11013) with
| (head3, uu____11025, t2) -> begin
((head3), (t2))
end))
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____11028; FStar_Extraction_ML_Syntax.loc = uu____11029})::[]) -> begin
(

let uu____11032 = (instantiate_maybe_partial head3 ((vars), (t1)) provided_type_args)
in (match (uu____11032) with
| (head4, uu____11044, t2) -> begin
(

let uu____11046 = (FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((head4), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
in ((uu____11046), (t2)))
end))
end
| uu____11049 -> begin
(failwith "Impossible: Unexpected head term")
end)
in (match (uu____10987) with
| (head3, t2) -> begin
((head3), (t2), (rest))
end))
end)))
end)
in (match (uu____10696) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____11116 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____11116), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____11117 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____11126) -> begin
(

let uu____11127 = (

let uu____11148 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____11148) with
| (FStar_Util.Inr (exp_b), q) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____11187 -> (

let uu____11188 = (FStar_Syntax_Print.term_to_string head2)
in (

let uu____11190 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule exp_b.FStar_Extraction_ML_UEnv.exp_b_expr)
in (

let uu____11192 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule (FStar_Pervasives_Native.snd exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme))
in (

let uu____11194 = (FStar_Util.string_of_bool exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)
in (FStar_Util.print4 "@@@looked up %s: got %s at %s (inst_ok=%s)\n" uu____11188 uu____11190 uu____11192 uu____11194)))))));
((((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr), (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme), (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok))), (q));
)
end
| uu____11221 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____11127) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____11297))::uu____11298 -> begin
(is_type g a)
end
| uu____11325 -> begin
false
end)
in (

let uu____11337 = (match (vars) with
| (uu____11366)::uu____11367 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____11381 -> begin
(

let n1 = (FStar_List.length vars)
in (

let uu____11387 = (match (((FStar_List.length args) <= n1)) with
| true -> begin
(

let uu____11425 = (FStar_List.map (fun uu____11437 -> (match (uu____11437) with
| (x, uu____11445) -> begin
(term_as_mlty g x)
end)) args)
in ((uu____11425), ([])))
end
| uu____11466 -> begin
(

let uu____11468 = (FStar_Util.first_N n1 args)
in (match (uu____11468) with
| (prefix1, rest) -> begin
(

let uu____11557 = (FStar_List.map (fun uu____11569 -> (match (uu____11569) with
| (x, uu____11577) -> begin
(term_as_mlty g x)
end)) prefix1)
in ((uu____11557), (rest)))
end))
end)
in (match (uu____11387) with
| (provided_type_args, rest) -> begin
(

let uu____11628 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____11637) -> begin
(

let uu____11638 = (instantiate_maybe_partial head_ml ((vars), (t1)) provided_type_args)
in (match (uu____11638) with
| (head3, uu____11650, t2) -> begin
((head3), (t2))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____11652) -> begin
(

let uu____11654 = (instantiate_maybe_partial head_ml ((vars), (t1)) provided_type_args)
in (match (uu____11654) with
| (head3, uu____11666, t2) -> begin
((head3), (t2))
end))
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____11669; FStar_Extraction_ML_Syntax.loc = uu____11670})::[]) -> begin
(

let uu____11673 = (instantiate_maybe_partial head3 ((vars), (t1)) provided_type_args)
in (match (uu____11673) with
| (head4, uu____11685, t2) -> begin
(

let uu____11687 = (FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((head4), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
in ((uu____11687), (t2)))
end))
end
| uu____11690 -> begin
(failwith "Impossible: Unexpected head term")
end)
in (match (uu____11628) with
| (head3, t2) -> begin
((head3), (t2), (rest))
end))
end)))
end)
in (match (uu____11337) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____11757 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____11757), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____11758 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____11767 -> begin
(

let uu____11768 = (term_as_mlexpr g head2)
in (match (uu____11768) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end)))
in (

let uu____11784 = (is_type g t)
in (match (uu____11784) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____11793 -> begin
(

let uu____11795 = (

let uu____11796 = (FStar_Syntax_Util.un_uinst head1)
in uu____11796.FStar_Syntax_Syntax.n)
in (match (uu____11795) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11806 = (FStar_Extraction_ML_UEnv.try_lookup_fv g fv)
in (match (uu____11806) with
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Erased))
end
| uu____11815 -> begin
(extract_app_with_instantiations ())
end))
end
| uu____11818 -> begin
(extract_app_with_instantiations ())
end))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____11821), f) -> begin
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

let uu____11889 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____11889) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____11924 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____11938 -> begin
(

let uu____11940 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____11940) with
| true -> begin
((lbs), (e'))
end
| uu____11951 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____11955 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____11955))
in (

let lb1 = (

let uu___1710_11957 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___1710_11957.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1710_11957.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___1710_11957.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___1710_11957.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___1710_11957.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1710_11957.FStar_Syntax_Syntax.lbpos})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____11924) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____11991 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.env_tcenv uu____11991))
in (

let lbdef = (

let uu____12006 = (FStar_Options.ml_ish ())
in (match (uu____12006) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____12011 -> begin
(

let norm_call = (fun uu____12018 -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.PureSubtermsWithinComputations)::extraction_norm_steps) tcenv lb.FStar_Syntax_Syntax.lbdef))
in (

let uu____12019 = ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("Extraction"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("ExtractNorm"))))
in (match (uu____12019) with
| true -> begin
((

let uu____12029 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____12031 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Util.print2 "Starting to normalize top-level let %s)\n\tlbdef=%s" uu____12029 uu____12031)));
(

let a = (

let uu____12037 = (

let uu____12039 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.format1 "###(Time to normalize top-level let %s)" uu____12039))
in (FStar_Util.measure_execution_time uu____12037 norm_call))
in ((

let uu____12045 = (FStar_Syntax_Print.term_to_string a)
in (FStar_Util.print1 "Normalized to %s\n" uu____12045));
a;
));
)
end
| uu____12048 -> begin
(norm_call ())
end)))
end))
in (

let uu___1728_12050 = lb
in {FStar_Syntax_Syntax.lbname = uu___1728_12050.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1728_12050.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1728_12050.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___1728_12050.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___1728_12050.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1728_12050.FStar_Syntax_Syntax.lbpos}))))))
end
| uu____12051 -> begin
lbs1
end)
in (

let check_lb = (fun env uu____12103 -> (match (uu____12103) with
| (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____12259 -> (match (uu____12259) with
| (a, uu____12267) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____12273 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____12273) with
| (e1, ty) -> begin
(

let uu____12284 = (maybe_promote_effect e1 f expected_t)
in (match (uu____12284) with
| (e2, f1) -> begin
(

let meta = (match (((f1), (ty))) with
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
(FStar_Extraction_ML_Syntax.Erased)::[]
end
| uu____12296 -> begin
[]
end)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e2; FStar_Extraction_ML_Syntax.mllb_meta = meta; FStar_Extraction_ML_Syntax.print_typ = true})))
end))
end))))
end))
in (

let lbs3 = (extract_lb_sig g ((is_rec), (lbs2)))
in (

let uu____12327 = (FStar_List.fold_right (fun lb uu____12424 -> (match (uu____12424) with
| (env, lbs4) -> begin
(

let uu____12558 = lb
in (match (uu____12558) with
| (lbname, uu____12609, (t1, (uu____12611, polytype)), add_unit, uu____12614) -> begin
(

let uu____12629 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____12629) with
| (env1, nm, uu____12670) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____12327) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____12855 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____12949 = (term_as_mlexpr env_body e'1)
in (match (uu____12949) with
| (e'2, f', t') -> begin
(

let f = (

let uu____12966 = (

let uu____12969 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____12969)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____12966))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____12980 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____12982 = (

let uu____12983 = (

let uu____12984 = (

let uu____12985 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), (uu____12985)))
in (mk_MLE_Let top_level uu____12984 e'2))
in (

let uu____12994 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____12983 uu____12994)))
in ((uu____12982), (f), (t')))))
end)))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____13033 = (term_as_mlexpr g scrutinee)
in (match (uu____13033) with
| (e, f_e, t_e) -> begin
(

let uu____13049 = (check_pats_for_ite pats)
in (match (uu____13049) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____13114 = (term_as_mlexpr g then_e1)
in (match (uu____13114) with
| (then_mle, f_then, t_then) -> begin
(

let uu____13130 = (term_as_mlexpr g else_e1)
in (match (uu____13130) with
| (else_mle, f_else, t_else) -> begin
(

let uu____13146 = (

let uu____13157 = (type_leq g t_then t_else)
in (match (uu____13157) with
| true -> begin
((t_else), (no_lift))
end
| uu____13176 -> begin
(

let uu____13178 = (type_leq g t_else t_then)
in (match (uu____13178) with
| true -> begin
((t_then), (no_lift))
end
| uu____13197 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____13146) with
| (t_branch, maybe_lift1) -> begin
(

let uu____13225 = (

let uu____13226 = (

let uu____13227 = (

let uu____13236 = (maybe_lift1 then_mle t_then)
in (

let uu____13237 = (

let uu____13240 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____13240))
in ((e), (uu____13236), (uu____13237))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____13227))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____13226))
in (

let uu____13243 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____13225), (uu____13243), (t_branch))))
end))
end))
end))
end
| uu____13244 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____13260 -> begin
(

let uu____13262 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____13361 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____13361) with
| (pat, when_opt, branch1) -> begin
(

let uu____13406 = (extract_pat g pat t_e term_as_mlexpr)
in (match (uu____13406) with
| (env, p, pat_t_compat) -> begin
(

let uu____13468 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let w_pos = w.FStar_Syntax_Syntax.pos
in (

let uu____13491 = (term_as_mlexpr env w)
in (match (uu____13491) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce w_pos env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end)))
end)
in (match (uu____13468) with
| (when_opt1, f_when) -> begin
(

let uu____13541 = (term_as_mlexpr env branch1)
in (match (uu____13541) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____13576 = (FStar_All.pipe_right p (FStar_List.map (fun uu____13653 -> (match (uu____13653) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____13576)))
end))
end))
end))
end))) true))
in (match (uu____13262) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____13818 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____13824 -> (

let uu____13825 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____13827 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____13825 uu____13827)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____13854 = (

let uu____13855 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____13855))
in (match (uu____13854) with
| {FStar_Extraction_ML_UEnv.exp_b_name = uu____13862; FStar_Extraction_ML_UEnv.exp_b_expr = fw; FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____13864; FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____13865} -> begin
(

let uu____13868 = (

let uu____13869 = (

let uu____13870 = (

let uu____13877 = (

let uu____13880 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____13880)::[])
in ((fw), (uu____13877)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____13870))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____13869))
in ((uu____13868), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| ((uu____13884, uu____13885, (uu____13886, f_first, t_first)))::rest -> begin
(

let uu____13946 = (FStar_List.fold_left (fun uu____13988 uu____13989 -> (match (((uu____13988), (uu____13989))) with
| ((topt, f), (uu____14046, uu____14047, (uu____14048, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____14104 = (type_leq g t1 t_branch)
in (match (uu____14104) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____14109 -> begin
(

let uu____14111 = (type_leq g t_branch t1)
in (match (uu____14111) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____14116 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____13946) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____14209 -> (match (uu____14209) with
| (p, (wopt, uu____14238), (b1, uu____14240, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____14259) -> begin
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

let uu____14264 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____14264), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____14291 = (

let uu____14296 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.env_tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14296))
in (match (uu____14291) with
| (uu____14321, fstar_disc_type) -> begin
(

let wildcards = (

let uu____14331 = (

let uu____14332 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____14332.FStar_Syntax_Syntax.n)
in (match (uu____14331) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____14343) -> begin
(

let uu____14364 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___2_14398 -> (match (uu___2_14398) with
| (uu____14406, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____14407))) -> begin
true
end
| uu____14412 -> begin
false
end))))
in (FStar_All.pipe_right uu____14364 (FStar_List.map (fun uu____14448 -> (

let uu____14455 = (fresh "_")
in ((uu____14455), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____14459 -> begin
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

let uu____14474 = (

let uu____14475 = (

let uu____14487 = (

let uu____14488 = (

let uu____14489 = (

let uu____14504 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____14510 = (

let uu____14521 = (

let uu____14530 = (

let uu____14531 = (

let uu____14538 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____14538), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____14531))
in (

let uu____14541 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____14530), (FStar_Pervasives_Native.None), (uu____14541))))
in (

let uu____14545 = (

let uu____14556 = (

let uu____14565 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____14565)))
in (uu____14556)::[])
in (uu____14521)::uu____14545))
in ((uu____14504), (uu____14510))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____14489))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____14488))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____14487)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____14475))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____14474))
in (

let uu____14626 = (

let uu____14627 = (

let uu____14630 = (

let uu____14631 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____14631; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____14630)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), (uu____14627)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____14626)))))))
end)))




