
open Prims
open FStar_Pervasives
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____4 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields : 'Auu____50 . FStar_Ident.ident Prims.list  ->  'Auu____50 Prims.list  ->  (Prims.string * 'Auu____50) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail : 'Auu____84 . FStar_Range.range  ->  (FStar_Errors.raw_error * Prims.string)  ->  'Auu____84 = (fun r err -> (FStar_Errors.raise_error err r))


let err_uninst : 'Auu____106 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Syntax_Syntax.term  ->  'Auu____106 = (fun env t uu____127 app -> (match (uu____127) with
| (vars, ty) -> begin
(

let uu____141 = (

let uu____146 = (

let uu____147 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____148 = (FStar_All.pipe_right vars (FStar_String.concat ", "))
in (

let uu____151 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____152 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____147 uu____148 uu____151 uu____152)))))
in ((FStar_Errors.Fatal_Uninstantiated), (uu____146)))
in (fail t.FStar_Syntax_Syntax.pos uu____141))
end))


let err_ill_typed_application : 'Auu____159 'Auu____160 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * 'Auu____159) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____160 = (fun env t args ty -> (

let uu____189 = (

let uu____194 = (

let uu____195 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____196 = (

let uu____197 = (FStar_All.pipe_right args (FStar_List.map (fun uu____215 -> (match (uu____215) with
| (x, uu____221) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____197 (FStar_String.concat " ")))
in (

let uu____224 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" uu____195 uu____196 uu____224))))
in ((FStar_Errors.Fatal_IllTyped), (uu____194)))
in (fail t.FStar_Syntax_Syntax.pos uu____189)))


let err_value_restriction : 'Auu____227 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____227 = (fun t -> (

let uu____236 = (

let uu____241 = (

let uu____242 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____243 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____242 uu____243)))
in ((FStar_Errors.Fatal_ValueRestriction), (uu____241)))
in (fail t.FStar_Syntax_Syntax.pos uu____236)))


let err_unexpected_eff : 'Auu____248 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  'Auu____248 = (fun t f0 f1 -> (

let uu____265 = (

let uu____270 = (

let uu____271 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____272 = (FStar_Extraction_ML_Util.eff_to_string f0)
in (

let uu____273 = (FStar_Extraction_ML_Util.eff_to_string f1)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" uu____271 uu____272 uu____273))))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____270)))
in (fail t.FStar_Syntax_Syntax.pos uu____265)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____288 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____288) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____293 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____293) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____304, c) -> begin
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
| uu____314 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____315 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____337 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____337) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____340 -> begin
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

let uu____354 = (

let uu____355 = (FStar_Syntax_Subst.compress t1)
in uu____355.FStar_Syntax_Syntax.n)
in (match (uu____354) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____358) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____383) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____410) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____418 = (FStar_Syntax_Util.unfold_lazy i)
in (is_arity env uu____418))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____419) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____436) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____437) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____438) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____445) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____446) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____447, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____465) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____467 = (

let uu____468 = (FStar_Syntax_Subst.compress t2)
in uu____468.FStar_Syntax_Syntax.n)
in (match (uu____467) with
| FStar_Syntax_Syntax.Tm_fvar (uu____471) -> begin
false
end
| uu____472 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____473) -> begin
(

let uu____488 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____488) with
| (head1, uu____504) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____526) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____532) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____537, body, uu____539) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____560, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____578, branches) -> begin
(match (branches) with
| ((uu____616, uu____617, e))::uu____619 -> begin
(is_arity env e)
end
| uu____666 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____690) -> begin
(

let uu____715 = (

let uu____716 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____716))
in (failwith uu____715))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____717 = (

let uu____718 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____718))
in (failwith uu____717))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____720 = (FStar_Syntax_Util.unfold_lazy i)
in (is_type_aux env uu____720))
end
| FStar_Syntax_Syntax.Tm_constant (uu____721) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____722) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____723) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____730) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____745, t2) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____771; FStar_Syntax_Syntax.index = uu____772; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____776; FStar_Syntax_Syntax.index = uu____777; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____782, uu____783) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____825) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____832) -> begin
(

let uu____853 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____853) with
| (uu____858, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____875 = (

let uu____880 = (

let uu____881 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____881)::[])
in (FStar_Syntax_Subst.open_term uu____880 body))
in (match (uu____875) with
| (uu____882, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____884, lbs), body) -> begin
(

let uu____901 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____901) with
| (uu____908, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____914, branches) -> begin
(match (branches) with
| (b)::uu____953 -> begin
(

let uu____998 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____998) with
| (uu____999, uu____1000, e) -> begin
(is_type_aux env e)
end))
end
| uu____1018 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1035) -> begin
false
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1043) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1049) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1080 -> (

let uu____1081 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1082 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1081 uu____1082)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1088 -> (match (b) with
| true -> begin
(

let uu____1089 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1090 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____1089 uu____1090)))
end
| uu____1091 -> begin
(

let uu____1092 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1093 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1092 uu____1093)))
end)));
b;
));
))


let is_type_binder : 'Auu____1097 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____1097)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1117 = (

let uu____1118 = (FStar_Syntax_Subst.compress t)
in uu____1118.FStar_Syntax_Syntax.n)
in (match (uu____1117) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1121; FStar_Syntax_Syntax.fv_delta = uu____1122; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1123; FStar_Syntax_Syntax.fv_delta = uu____1124; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1125))}) -> begin
true
end
| uu____1132 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1136 = (

let uu____1137 = (FStar_Syntax_Subst.compress t)
in uu____1137.FStar_Syntax_Syntax.n)
in (match (uu____1136) with
| FStar_Syntax_Syntax.Tm_constant (uu____1140) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1141) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1142) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1143) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1182 = (is_constructor head1)
in (match (uu____1182) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1198 -> (match (uu____1198) with
| (te, uu____1204) -> begin
(is_fstar_value te)
end))))
end
| uu____1205 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1207) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1213, uu____1214) -> begin
(is_fstar_value t1)
end
| uu____1255 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1259) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1260) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1261) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1262) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1273, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1282, fields) -> begin
(FStar_Util.for_all (fun uu____1307 -> (match (uu____1307) with
| (uu____1312, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1315) -> begin
(is_ml_value h)
end
| uu____1320 -> begin
false
end))


let fresh : Prims.string  ->  Prims.string = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1433 = (

let uu____1434 = (FStar_ST.op_Bang c)
in (FStar_Util.string_of_int uu____1434))
in (Prims.strcat x uu____1433));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1587 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1589 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1589) with
| true -> begin
(aux bs e' copt)
end
| uu____1590 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1595 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1595))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1672 -> begin
(

let uu____1673 = (FStar_List.hd l)
in (match (uu____1673) with
| (p1, w1, e1) -> begin
(

let uu____1707 = (

let uu____1716 = (FStar_List.tl l)
in (FStar_List.hd uu____1716))
in (match (uu____1707) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1790 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_GHOST) || ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1847 = (erasable g f ty)
in (match (uu____1847) with
| true -> begin
(

let uu____1848 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1848) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1849 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1850 -> begin
e
end))
in ((e1), (f), (ty))))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____1857 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1857) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____1872 -> begin
(

let vs = (FStar_List.map (fun uu____1877 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____1888 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____1902 -> (match (uu____1902) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____1888))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____1924 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____1926 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1926 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))))
in (match (uu____1924) with
| true -> begin
e
end
| uu____1931 -> begin
(eta_expand expect e)
end)))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1945 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____1945) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____1955 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1967 -> (

let uu____1968 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1969 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1970 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1968 uu____1969 uu____1970))))));
(

let uu____1971 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))))
in (maybe_eta_expand expect uu____1971));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1978 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1978) with
| FStar_Util.Inl (uu____1979, t) -> begin
t
end
| uu____1993 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____2036) -> begin
(

let uu____2043 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____2043) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____2047 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____2050 = (is_top_ty mlt)
in (match (uu____2050) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____2052 -> begin
mlt
end))))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____2056) -> begin
(

let uu____2057 = (

let uu____2058 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2058))
in (failwith uu____2057))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2059) -> begin
(

let uu____2084 = (

let uu____2085 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2085))
in (failwith uu____2084))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2086 = (

let uu____2087 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____2087))
in (failwith uu____2086))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2089 = (FStar_Syntax_Util.unfold_lazy i)
in (term_as_mlty' env uu____2089))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2090) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_quoted (uu____2091) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2098) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____2116) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____2121; FStar_Syntax_Syntax.index = uu____2122; FStar_Syntax_Syntax.sort = t2}, uu____2124) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2132) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2138, uu____2139) -> begin
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

let uu____2206 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2206) with
| (bs1, c1) -> begin
(

let uu____2213 = (binders_as_ml_binders env bs1)
in (match (uu____2213) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2240 = (

let uu____2247 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____2247))
in (match (uu____2240) with
| (ed, qualifiers) -> begin
(

let uu____2268 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____2268) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____2273 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2275 = (FStar_List.fold_right (fun uu____2294 uu____2295 -> (match (((uu____2294), (uu____2295))) with
| ((uu____2316, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____2275) with
| (uu____2328, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____2353 = (

let uu____2354 = (FStar_Syntax_Util.un_uinst head1)
in uu____2354.FStar_Syntax_Syntax.n)
in (match (uu____2353) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____2381 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____2381))
end
| uu____2398 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2401) -> begin
(

let uu____2422 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____2422) with
| (bs1, ty1) -> begin
(

let uu____2429 = (binders_as_ml_binders env bs1)
in (match (uu____2429) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2454) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_let (uu____2455) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____2468) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____2492 -> (match (uu____2492) with
| (a, uu____2498) -> begin
(

let uu____2499 = (is_type g a)
in (match (uu____2499) with
| true -> begin
(term_as_mlty' g a)
end
| uu____2500 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____2504 = (

let uu____2517 = (FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2517) with
| ((uu____2538, fvty), uu____2540) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) g.FStar_Extraction_ML_UEnv.tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____2504) with
| (formals, uu____2547) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____2591 = (FStar_Util.first_N n_args formals)
in (match (uu____2591) with
| (uu____2618, rest) -> begin
(

let uu____2644 = (FStar_List.map (fun uu____2652 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____2644))
end))
end
| uu____2657 -> begin
mlargs
end))
in (

let nm = (

let uu____2659 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____2659) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____2677 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2720 b -> (match (uu____2720) with
| (ml_bs, env) -> begin
(

let uu____2760 = (is_type_binder g b)
in (match (uu____2760) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____2778 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____2778), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____2789 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____2792 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____2792) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____2816 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____2816), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____2677) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____2884) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____2887, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____2891 -> begin
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
| uu____2917 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____2919 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____2920 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____2921 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____2924 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____2941 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____2941) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____2945 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____2972 -> begin
p
end)
end))
end
| uu____2975 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____3055 -> (

let uu____3056 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____3057 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____3056 uu____3057)))))
end
| uu____3058 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, swopt)) when (

let uu____3087 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____3087 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin)))) -> begin
(

let uu____3092 = (match (swopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3105 = (

let uu____3106 = (

let uu____3107 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (((c), (FStar_Pervasives_Native.None)))))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____3107))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____3106))
in ((uu____3105), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end
| FStar_Pervasives_Native.Some (sw) -> begin
(

let source_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer g.FStar_Extraction_ML_UEnv.tcenv.FStar_TypeChecker_Env.dsenv c sw FStar_Range.dummyRange)
in (

let uu____3128 = (term_as_mlexpr g source_term)
in (match (uu____3128) with
| (mlterm, uu____3140, mlty) -> begin
((mlterm), (mlty))
end)))
end)
in (match (uu____3092) with
| (mlc, ml_ty) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____3160 = (

let uu____3161 = (

let uu____3168 = (

let uu____3171 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ml_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____3171)::(mlc)::[])
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____3168)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3161))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3160))
in (

let uu____3174 = (ok ml_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____3174)))))
end))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____3194 = (

let uu____3203 = (

let uu____3210 = (

let uu____3211 = (FStar_Extraction_ML_Util.mlconst_of_const p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____3211))
in ((uu____3210), ([])))
in FStar_Pervasives_Native.Some (uu____3203))
in (

let uu____3220 = (ok mlty)
in ((g), (uu____3194), (uu____3220))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3231 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3231) with
| (g1, x1) -> begin
(

let uu____3254 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3277 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3254)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3288 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3288) with
| (g1, x1) -> begin
(

let uu____3311 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3334 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3311)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____3343) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____3382 = (

let uu____3387 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____3387) with
| FStar_Util.Inr (uu____3392, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____3394; FStar_Extraction_ML_Syntax.loc = uu____3395}, ttys, uu____3397) -> begin
((n1), (ttys))
end
| uu____3410 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____3382) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____3432 = (FStar_Util.first_N nTyVars pats)
in (match (uu____3432) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___65_3532 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____3565 -> (match (uu____3565) with
| (p1, uu____3573) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____3578, t) -> begin
(term_as_mlty g t)
end
| uu____3584 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3588 -> (

let uu____3589 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____3589))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____3591 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____3591))))
end)) (fun uu___64_3605 -> (match (uu___64_3605) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____3620 = (FStar_Util.fold_map (fun g1 uu____3656 -> (match (uu____3656) with
| (p1, imp1) -> begin
(

let uu____3675 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None term_as_mlexpr)
in (match (uu____3675) with
| (g2, p2, uu____3704) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____3620) with
| (g1, tyMLPats) -> begin
(

let uu____3765 = (FStar_Util.fold_map (fun uu____3829 uu____3830 -> (match (((uu____3829), (uu____3830))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____3923 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____3983 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____3923) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____4054 = (extract_one_pat false g2 p1 expected_ty term_as_mlexpr)
in (match (uu____4054) with
| (g3, p2, uu____4095) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____3765) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____4213 = (

let uu____4224 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___61_4275 -> (match (uu___61_4275) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____4317 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4224 FStar_List.split))
in (match (uu____4213) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____4390 -> begin
false
end)
in (

let uu____4399 = (

let uu____4408 = (

let uu____4415 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____4418 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____4415), (uu____4418))))
in FStar_Pervasives_Native.Some (uu____4408))
in ((g2), (uu____4399), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty))  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t term_as_mlexpr -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____4531 = (extract_one_pat false g1 p1 expected_t1 term_as_mlexpr)
in (match (uu____4531) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____4588 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____4631 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____4631))
end))
in (

let uu____4632 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____4632) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____4770, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____4773 = (

let uu____4784 = (

let uu____4793 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____4793)))
in (uu____4784)::more_args)
in (eta_args uu____4773 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____4806, uu____4807) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____4830 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____4858, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____4890 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____4908 = (eta_args [] residualType)
in (match (uu____4908) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____4961 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____4961))
end
| uu____4962 -> begin
(

let uu____4973 = (FStar_List.unzip eargs)
in (match (uu____4973) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____5015 = (

let uu____5016 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____5016))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____5015))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____5025 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____5028, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5032; FStar_Extraction_ML_Syntax.loc = uu____5033}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____5060 -> begin
(

let uu____5063 = (

let uu____5070 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____5070), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5063))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5074; FStar_Extraction_ML_Syntax.loc = uu____5075}, uu____5076); FStar_Extraction_ML_Syntax.mlty = uu____5077; FStar_Extraction_ML_Syntax.loc = uu____5078}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____5109 -> begin
(

let uu____5112 = (

let uu____5119 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____5119), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5112))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5123; FStar_Extraction_ML_Syntax.loc = uu____5124}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5132 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5132))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5136; FStar_Extraction_ML_Syntax.loc = uu____5137}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5139))) -> begin
(

let uu____5152 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5152))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5156; FStar_Extraction_ML_Syntax.loc = uu____5157}, uu____5158); FStar_Extraction_ML_Syntax.mlty = uu____5159; FStar_Extraction_ML_Syntax.loc = uu____5160}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5172 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5172))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5176; FStar_Extraction_ML_Syntax.loc = uu____5177}, uu____5178); FStar_Extraction_ML_Syntax.mlty = uu____5179; FStar_Extraction_ML_Syntax.loc = uu____5180}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5182))) -> begin
(

let uu____5199 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5199))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5205 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5205))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5209))) -> begin
(

let uu____5218 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5218))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5222; FStar_Extraction_ML_Syntax.loc = uu____5223}, uu____5224), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5231 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5231))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5235; FStar_Extraction_ML_Syntax.loc = uu____5236}, uu____5237), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5238))) -> begin
(

let uu____5251 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5251))
end
| uu____5254 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let rec non_informative1 = (fun t1 -> (

let uu____5274 = ((type_leq g t1 FStar_Extraction_ML_Syntax.ml_unit_ty) || (erasableType g t1))
in (match (uu____5274) with
| true -> begin
true
end
| uu____5275 -> begin
(match (t1) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5276, FStar_Extraction_ML_Syntax.E_PURE, t2) -> begin
(non_informative1 t2)
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5278, FStar_Extraction_ML_Syntax.E_GHOST, t2) -> begin
(non_informative1 t2)
end
| uu____5280 -> begin
false
end)
end)))
in (

let uu____5281 = ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_GHOST) && (non_informative1 t))
in (match (uu____5281) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____5282 -> begin
f
end))))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____5335 = (term_as_mlexpr' g t)
in (match (uu____5335) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5356 = (

let uu____5357 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5358 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5359 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____5360 = (FStar_Extraction_ML_Util.eff_to_string tag1)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____5357 uu____5358 uu____5359 uu____5360)))))
in (FStar_Util.print_string uu____5356))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____5369 = (check_term_as_mlexpr' g t f ty)
in (match (uu____5369) with
| (e, t1) -> begin
(

let uu____5380 = (erase g e t1 f)
in (match (uu____5380) with
| (r, uu____5392, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____5402 = (term_as_mlexpr g e0)
in (match (uu____5402) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (

let uu____5417 = (FStar_Extraction_ML_Util.eff_leq tag1 f)
in (match (uu____5417) with
| true -> begin
(

let uu____5422 = (maybe_coerce g e t ty)
in ((uu____5422), (ty)))
end
| uu____5423 -> begin
(err_unexpected_eff e0 f tag1)
end)))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5440 = (

let uu____5441 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5442 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____5443 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____5441 uu____5442 uu____5443))))
in (FStar_Util.print_string uu____5440))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5451 = (

let uu____5452 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5452))
in (failwith uu____5451))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5459) -> begin
(

let uu____5484 = (

let uu____5485 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5485))
in (failwith uu____5484))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5492) -> begin
(

let uu____5509 = (

let uu____5510 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5510))
in (failwith uu____5509))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5517) -> begin
(

let uu____5518 = (

let uu____5519 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5519))
in (failwith uu____5518))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5527 = (FStar_Syntax_Util.unfold_lazy i)
in (term_as_mlexpr' g uu____5527))
end
| FStar_Syntax_Syntax.Tm_type (uu____5528) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5529) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5536) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____5550}) -> begin
(

let uu____5565 = (

let uu____5574 = (

let uu____5591 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____5591))
in (FStar_All.pipe_left FStar_Util.right uu____5574))
in (match (uu____5565) with
| (uu____5634, fw, uu____5636, uu____5637) -> begin
(

let uu____5638 = (

let uu____5639 = (

let uu____5640 = (

let uu____5647 = (

let uu____5650 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Open quotation at runtime"))))
in (uu____5650)::[])
in ((fw), (uu____5647)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5640))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____5639))
in ((uu____5638), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aqs}) -> begin
(

let uu____5669 = (FStar_Reflection_Basic.inspect_ln qt)
in (match (uu____5669) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____5677 = (FStar_Syntax_Syntax.lookup_aq bv aqs)
in (match (uu____5677) with
| FStar_Pervasives_Native.Some (false, tm) -> begin
(term_as_mlexpr' g tm)
end
| FStar_Pervasives_Native.Some (true, tm) -> begin
(

let uu____5700 = (

let uu____5709 = (

let uu____5726 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____5726))
in (FStar_All.pipe_left FStar_Util.right uu____5709))
in (match (uu____5700) with
| (uu____5769, fw, uu____5771, uu____5772) -> begin
(

let uu____5773 = (

let uu____5774 = (

let uu____5775 = (

let uu____5782 = (

let uu____5785 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("Open quotation at runtime"))))
in (uu____5785)::[])
in ((fw), (uu____5782)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5775))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____5774))
in ((uu____5773), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let tv = (

let uu____5793 = (FStar_Reflection_Embeddings.embed_term_view_aq aqs)
in (uu____5793 t.FStar_Syntax_Syntax.pos (FStar_Reflection_Data.Tv_Var (bv))))
in (

let t1 = (

let uu____5802 = (

let uu____5811 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____5811)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____5802))
in (term_as_mlexpr' g t1)))
end))
end
| tv -> begin
(

let tv1 = (

let uu____5814 = (FStar_Reflection_Embeddings.embed_term_view_aq aqs)
in (uu____5814 t.FStar_Syntax_Syntax.pos tv))
in (

let t1 = (

let uu____5823 = (

let uu____5832 = (FStar_Syntax_Syntax.as_arg tv1)
in (uu____5832)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____5823))
in (term_as_mlexpr' g t1)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Error_NoLetMutable), ("let-mutable no longer supported")))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____5846)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____5876 = (

let uu____5883 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____5883))
in (match (uu____5876) with
| (ed, qualifiers) -> begin
(

let uu____5910 = (

let uu____5911 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____5911 Prims.op_Negation))
in (match (uu____5910) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____5920 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____5927 -> begin
(term_as_mlexpr' g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5929) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5935) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____5941 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____5941) with
| (uu____5954, ty, uu____5956) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____5958 = (

let uu____5959 = (FStar_Extraction_ML_Util.mlexpr_of_const t.FStar_Syntax_Syntax.pos c)
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5959))
in ((uu____5958), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____5960) -> begin
(

let uu____5961 = (is_type g t)
in (match (uu____5961) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5968 -> begin
(

let uu____5969 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5969) with
| (FStar_Util.Inl (uu____5982), uu____5983) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____6020, x, mltys, uu____6023), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____6069 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____6069), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____6070 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6077) -> begin
(

let uu____6078 = (is_type g t)
in (match (uu____6078) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____6085 -> begin
(

let uu____6086 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____6086) with
| (FStar_Util.Inl (uu____6099), uu____6100) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____6137, x, mltys, uu____6140), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____6186 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____6186), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____6187 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____6217 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____6217) with
| (bs1, body1) -> begin
(

let uu____6230 = (binders_as_ml_binders g bs1)
in (match (uu____6230) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____6263 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____6263) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____6264 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____6268 -> (

let uu____6269 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____6269))));
body1;
)
end)
in (

let uu____6270 = (term_as_mlexpr env body2)
in (match (uu____6270) with
| (ml_body, f, t1) -> begin
(

let uu____6286 = (FStar_List.fold_right (fun uu____6305 uu____6306 -> (match (((uu____6305), (uu____6306))) with
| ((uu____6327, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____6286) with
| (f1, tfun) -> begin
(

let uu____6347 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____6347), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____6354; FStar_Syntax_Syntax.vars = uu____6355}, ((a1, uu____6357))::[]) -> begin
(

let ty = (

let uu____6387 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (term_as_mlty g uu____6387))
in (

let uu____6388 = (

let uu____6389 = (FStar_Extraction_ML_Util.mlexpr_of_range a1.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) uu____6389))
in ((uu____6388), (FStar_Extraction_ML_Syntax.E_PURE), (ty))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____6390; FStar_Syntax_Syntax.vars = uu____6391}, ((t1, uu____6393))::((r, uu____6395))::[]) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6434)); FStar_Syntax_Syntax.pos = uu____6435; FStar_Syntax_Syntax.vars = uu____6436}, uu____6437) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___62_6493 -> (match (uu___62_6493) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6494 -> begin
false
end))))))
in (

let uu____6495 = (

let uu____6500 = (

let uu____6501 = (FStar_Syntax_Subst.compress head1)
in uu____6501.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____6500)))
in (match (uu____6495) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6510), uu____6511) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6529, FStar_Syntax_Syntax.Tm_abs (bs, uu____6531, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6552, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____6554 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6554))
in (

let tm = (

let uu____6564 = (

let uu____6565 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____6566 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6565 uu____6566)))
in (uu____6564 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr' g tm)))
end
| uu____6575 -> begin
(

let rec extract_app = (fun is_data uu____6620 uu____6621 restArgs -> (match (((uu____6620), (uu____6621))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____6711) -> begin
(

let evaluation_order_guaranteed = (((Prims.op_Equality (FStar_List.length mlargs_f) (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____6733 -> begin
false
end))
in (

let uu____6734 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____6759 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (([]), (uu____6759)))
end
| uu____6790 -> begin
(FStar_List.fold_left (fun uu____6813 uu____6814 -> (match (((uu____6813), (uu____6814))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((Prims.op_Equality f1 FStar_Extraction_ML_Syntax.E_PURE) || (Prims.op_Equality f1 FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____6915 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____6917 = (

let uu____6920 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____6920)::out_args)
in (((((x), (arg)))::lbs), (uu____6917))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____6734) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____6970 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____6970))
in (

let l_app = (FStar_List.fold_right (fun uu____6982 out -> (match (uu____6982) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____7001))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____7032 = (

let uu____7037 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____7037), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____7032 rest))
end
| (((e0, uu____7049))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____7081 = (term_as_mlexpr g e0)
in (match (uu____7081) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____7098 = (

let uu____7103 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____7103), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____7098 rest)))
end)))
end
| uu____7114 -> begin
(

let uu____7127 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____7127) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____7184 args1 -> (match (uu____7184) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____7216)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____7294))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____7296, f', t3)) -> begin
(

let uu____7333 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____7333 t3))
end
| uu____7334 -> begin
((args2), (f1), (t2))
end))
in (

let uu____7359 = (remove_implicits args1 f t1)
in (match (uu____7359) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____7415 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____7428 = (is_type g t)
in (match (uu____7428) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____7435 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (uu____7443) -> begin
(

let uu____7444 = (

let uu____7457 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7457) with
| (FStar_Util.Inr (uu____7476, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7521 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7444) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7571))::uu____7572 -> begin
(is_type g a)
end
| uu____7591 -> begin
false
end)
in (

let uu____7600 = (match (vars) with
| (uu____7629)::uu____7630 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7641 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7669 = (FStar_Util.first_N n1 args)
in (match (uu____7669) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7758 -> (match (uu____7758) with
| (x, uu____7764) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____7777 -> begin
(

let uu___66_7780 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___66_7780.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___66_7780.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7784) -> begin
(

let uu___67_7785 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___67_7785.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___67_7785.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7786) -> begin
(

let uu___67_7787 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___67_7787.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___67_7787.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7789; FStar_Extraction_ML_Syntax.loc = uu____7790})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___68_7796 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___68_7796.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___68_7796.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7797 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____7806 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7600) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7858 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7858), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7859 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7868) -> begin
(

let uu____7869 = (

let uu____7882 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7882) with
| (FStar_Util.Inr (uu____7901, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7946 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7869) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7996))::uu____7997 -> begin
(is_type g a)
end
| uu____8016 -> begin
false
end)
in (

let uu____8025 = (match (vars) with
| (uu____8054)::uu____8055 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____8066 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____8094 = (FStar_Util.first_N n1 args)
in (match (uu____8094) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____8183 -> (match (uu____8183) with
| (x, uu____8189) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____8202 -> begin
(

let uu___66_8205 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___66_8205.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___66_8205.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____8209) -> begin
(

let uu___67_8210 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___67_8210.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___67_8210.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____8211) -> begin
(

let uu___67_8212 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___67_8212.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___67_8212.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____8214; FStar_Extraction_ML_Syntax.loc = uu____8215})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___68_8221 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___68_8221.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___68_8221.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____8222 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____8231 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____8025) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____8283 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____8283), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____8284 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____8293 -> begin
(

let uu____8294 = (term_as_mlexpr g head2)
in (match (uu____8294) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____8312), f) -> begin
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

let uu____8379 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____8379) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____8410 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____8423 -> begin
(

let uu____8424 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____8424) with
| true -> begin
((lbs), (e'))
end
| uu____8435 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____8438 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____8438))
in (

let lb1 = (

let uu___69_8440 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___69_8440.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___69_8440.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___69_8440.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___69_8440.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___69_8440.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___69_8440.FStar_Syntax_Syntax.lbpos})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____8410) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____8472 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____8472))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____8479 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____8483 = (FStar_Options.ml_ish ())
in (match (uu____8483) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____8486 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___70_8487 = lb
in {FStar_Syntax_Syntax.lbname = uu___70_8487.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___70_8487.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___70_8487.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___70_8487.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___70_8487.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___70_8487.FStar_Syntax_Syntax.lbpos}));
)))))
end
| uu____8488 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____8510 -> (match (uu____8510) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____8530; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____8534; FStar_Syntax_Syntax.lbpos = uu____8535} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (

let no_gen = (fun uu____8609 -> (

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e))))
in (match ((not (top_level))) with
| true -> begin
(no_gen ())
end
| uu____8689 -> begin
(match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____8726 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____8726 (is_type_binder g))) -> begin
(

let uu____8739 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8739) with
| (bs1, c1) -> begin
(

let uu____8764 = (

let uu____8771 = (FStar_Util.prefix_until (fun x -> (

let uu____8807 = (is_type_binder g x)
in (not (uu____8807)))) bs1)
in (match (uu____8771) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____8895 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____8895)))
end))
in (match (uu____8764) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____8940 = (normalize_abs e)
in (FStar_All.pipe_right uu____8940 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____8982 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____8982) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____9035 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____9035) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____9123 uu____9124 -> (match (((uu____9123), (uu____9124))) with
| ((x, uu____9142), (y, uu____9144)) -> begin
(

let uu____9153 = (

let uu____9160 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____9160)))
in FStar_Syntax_Syntax.NT (uu____9153))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____9171 -> (match (uu____9171) with
| (a, uu____9177) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____9186 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____9204 -> (match (uu____9204) with
| (x, uu____9210) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9186), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____9218 = (is_fstar_value body1)
in (not (uu____9218)))
end
| uu____9219 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____9231 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____9233 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((t2), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____9269 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____9288) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9305 -> (match (uu____9305) with
| (a, uu____9311) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9320 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9332 -> (match (uu____9332) with
| (x, uu____9338) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9320), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9354 -> (match (uu____9354) with
| (bv, uu____9360) -> begin
(

let uu____9361 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9361 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____9403) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9414 -> (match (uu____9414) with
| (a, uu____9420) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9429 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9441 -> (match (uu____9441) with
| (x, uu____9447) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9429), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9463 -> (match (uu____9463) with
| (bv, uu____9469) -> begin
(

let uu____9470 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9470 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____9512) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9523 -> (match (uu____9523) with
| (a, uu____9529) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9538 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9550 -> (match (uu____9550) with
| (x, uu____9556) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9538), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9572 -> (match (uu____9572) with
| (bv, uu____9578) -> begin
(

let uu____9579 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9579 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____9621 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____9640 -> begin
(no_gen ())
end)
end))))
end))
in (

let check_lb = (fun env uu____9683 -> (match (uu____9683) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____9818 -> (match (uu____9818) with
| (a, uu____9824) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____9826 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____9826) with
| (e1, uu____9836) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____9903 = (FStar_List.fold_right (fun lb uu____9994 -> (match (uu____9994) with
| (env, lbs4) -> begin
(

let uu____10119 = lb
in (match (uu____10119) with
| (lbname, uu____10167, (t1, (uu____10169, polytype)), add_unit, uu____10172) -> begin
(

let uu____10185 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____10185) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____9903) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____10387 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____10462 = (term_as_mlexpr env_body e'1)
in (match (uu____10462) with
| (e'2, f', t') -> begin
(

let f = (

let uu____10479 = (

let uu____10482 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____10482)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____10479))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____10490 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____10491 = (

let uu____10492 = (

let uu____10493 = (

let uu____10494 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), (uu____10494)))
in (mk_MLE_Let top_level uu____10493 e'2))
in (

let uu____10503 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____10492 uu____10503)))
in ((uu____10491), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____10542 = (term_as_mlexpr g scrutinee)
in (match (uu____10542) with
| (e, f_e, t_e) -> begin
(

let uu____10558 = (check_pats_for_ite pats)
in (match (uu____10558) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____10615 = (term_as_mlexpr g then_e1)
in (match (uu____10615) with
| (then_mle, f_then, t_then) -> begin
(

let uu____10631 = (term_as_mlexpr g else_e1)
in (match (uu____10631) with
| (else_mle, f_else, t_else) -> begin
(

let uu____10647 = (

let uu____10656 = (type_leq g t_then t_else)
in (match (uu____10656) with
| true -> begin
((t_else), (no_lift))
end
| uu____10669 -> begin
(

let uu____10670 = (type_leq g t_else t_then)
in (match (uu____10670) with
| true -> begin
((t_then), (no_lift))
end
| uu____10683 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____10647) with
| (t_branch, maybe_lift1) -> begin
(

let uu____10704 = (

let uu____10705 = (

let uu____10706 = (

let uu____10715 = (maybe_lift1 then_mle t_then)
in (

let uu____10716 = (

let uu____10719 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____10719))
in ((e), (uu____10715), (uu____10716))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____10706))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____10705))
in (

let uu____10722 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____10704), (uu____10722), (t_branch))))
end))
end))
end))
end
| uu____10723 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____10738 -> begin
(

let uu____10739 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____10848 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____10848) with
| (pat, when_opt, branch1) -> begin
(

let uu____10892 = (extract_pat g pat t_e term_as_mlexpr)
in (match (uu____10892) with
| (env, p, pat_t_compat) -> begin
(

let uu____10950 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____10972 = (term_as_mlexpr env w)
in (match (uu____10972) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end))
end)
in (match (uu____10950) with
| (when_opt1, f_when) -> begin
(

let uu____11021 = (term_as_mlexpr env branch1)
in (match (uu____11021) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____11055 = (FStar_All.pipe_right p (FStar_List.map (fun uu____11132 -> (match (uu____11132) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____11055)))
end))
end))
end))
end))) true))
in (match (uu____10739) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____11292 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____11297 -> (

let uu____11298 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____11299 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____11298 uu____11299)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____11324 = (

let uu____11333 = (

let uu____11350 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____11350))
in (FStar_All.pipe_left FStar_Util.right uu____11333))
in (match (uu____11324) with
| (uu____11393, fw, uu____11395, uu____11396) -> begin
(

let uu____11397 = (

let uu____11398 = (

let uu____11399 = (

let uu____11406 = (

let uu____11409 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____11409)::[])
in ((fw), (uu____11406)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____11399))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____11398))
in ((uu____11397), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_int_ty)))
end))
end
| ((uu____11412, uu____11413, (uu____11414, f_first, t_first)))::rest -> begin
(

let uu____11474 = (FStar_List.fold_left (fun uu____11516 uu____11517 -> (match (((uu____11516), (uu____11517))) with
| ((topt, f), (uu____11574, uu____11575, (uu____11576, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____11632 = (type_leq g t1 t_branch)
in (match (uu____11632) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____11635 -> begin
(

let uu____11636 = (type_leq g t_branch t1)
in (match (uu____11636) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____11639 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____11474) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____11731 -> (match (uu____11731) with
| (p, (wopt, uu____11760), (b1, uu____11762, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____11781) -> begin
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

let uu____11786 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____11786), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____11806 = (

let uu____11811 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11811))
in (match (uu____11806) with
| (uu____11836, fstar_disc_type) -> begin
(

let wildcards = (

let uu____11845 = (

let uu____11846 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____11846.FStar_Syntax_Syntax.n)
in (match (uu____11845) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11856) -> begin
(

let uu____11873 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___63_11905 -> (match (uu___63_11905) with
| (uu____11912, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11913))) -> begin
true
end
| uu____11916 -> begin
false
end))))
in (FStar_All.pipe_right uu____11873 (FStar_List.map (fun uu____11949 -> (

let uu____11956 = (fresh "_")
in ((uu____11956), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____11957 -> begin
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

let uu____11968 = (

let uu____11969 = (

let uu____11980 = (

let uu____11981 = (

let uu____11982 = (

let uu____11997 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____12000 = (

let uu____12011 = (

let uu____12020 = (

let uu____12021 = (

let uu____12028 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____12028), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____12021))
in (

let uu____12031 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____12020), (FStar_Pervasives_Native.None), (uu____12031))))
in (

let uu____12034 = (

let uu____12045 = (

let uu____12054 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____12054)))
in (uu____12045)::[])
in (uu____12011)::uu____12034))
in ((uu____11997), (uu____12000))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____11982))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11981))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____11980)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____11969))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11968))
in (

let uu____12109 = (

let uu____12110 = (

let uu____12113 = (

let uu____12114 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____12114; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.mllb_meta = []; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____12113)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), (uu____12110)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____12109)))))))
end)))




