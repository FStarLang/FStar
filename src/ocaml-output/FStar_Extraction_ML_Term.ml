
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


let record_fields : 'Auu____65 . FStar_Ident.ident Prims.list  ->  'Auu____65 Prims.list  ->  (Prims.string * 'Auu____65) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail : 'Auu____102 . FStar_Range.range  ->  Prims.string  ->  'Auu____102 = (fun r msg -> ((

let uu____112 = (

let uu____113 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____113 msg))
in (FStar_All.pipe_left FStar_Util.print_string uu____112));
(failwith msg);
))


let err_uninst : 'Auu____124 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (Prims.string Prims.list * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Syntax_Syntax.term  ->  'Auu____124 = (fun env t uu____145 app -> (match (uu____145) with
| (vars, ty) -> begin
(

let uu____159 = (

let uu____160 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____161 = (FStar_All.pipe_right vars (FStar_String.concat ", "))
in (

let uu____164 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____165 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____160 uu____161 uu____164 uu____165)))))
in (fail t.FStar_Syntax_Syntax.pos uu____159))
end))


let err_ill_typed_application : 'Auu____178 'Auu____179 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * 'Auu____179) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____178 = (fun env t args ty -> (

let uu____208 = (

let uu____209 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____210 = (

let uu____211 = (FStar_All.pipe_right args (FStar_List.map (fun uu____229 -> (match (uu____229) with
| (x, uu____235) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____211 (FStar_String.concat " ")))
in (

let uu____238 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" uu____209 uu____210 uu____238))))
in (fail t.FStar_Syntax_Syntax.pos uu____208)))


let err_value_restriction : 'Auu____243 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____243 = (fun t -> (

let uu____252 = (

let uu____253 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____254 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____253 uu____254)))
in (fail t.FStar_Syntax_Syntax.pos uu____252)))


let err_unexpected_eff : 'Auu____263 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  'Auu____263 = (fun t f0 f1 -> (

let uu____280 = (

let uu____281 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" uu____281 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos uu____280)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____298 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____298) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____303 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____303) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____314, c) -> begin
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
| uu____324 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____325 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____347 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____347) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____350 -> begin
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

let uu____366 = (

let uu____367 = (FStar_Syntax_Subst.compress t1)
in uu____367.FStar_Syntax_Syntax.n)
in (match (uu____366) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____370) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____395) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____422) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____429) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____446) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____447) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____448) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____449) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____450, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____468) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____470 = (

let uu____471 = (FStar_Syntax_Subst.compress t2)
in uu____471.FStar_Syntax_Syntax.n)
in (match (uu____470) with
| FStar_Syntax_Syntax.Tm_fvar (uu____474) -> begin
false
end
| uu____475 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____476) -> begin
(

let uu____491 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____491) with
| (head1, uu____507) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____529) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____535) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____540, body, uu____542) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____563, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____581, branches) -> begin
(match (branches) with
| ((uu____619, uu____620, e))::uu____622 -> begin
(is_arity env e)
end
| uu____669 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____695) -> begin
(

let uu____720 = (

let uu____721 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____721))
in (failwith uu____720))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____722 = (

let uu____723 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____723))
in (failwith uu____722))
end
| FStar_Syntax_Syntax.Tm_constant (uu____724) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____725) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____726) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____733) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____748, t2) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____774; FStar_Syntax_Syntax.index = uu____775; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____779; FStar_Syntax_Syntax.index = uu____780; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____785, uu____786) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____828) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____835) -> begin
(

let uu____856 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____856) with
| (uu____861, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____878 = (

let uu____883 = (

let uu____884 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____884)::[])
in (FStar_Syntax_Subst.open_term uu____883 body))
in (match (uu____878) with
| (uu____885, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____887, lbs), body) -> begin
(

let uu____904 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____904) with
| (uu____911, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____917, branches) -> begin
(match (branches) with
| (b)::uu____956 -> begin
(

let uu____1001 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____1001) with
| (uu____1002, uu____1003, e) -> begin
(is_type_aux env e)
end))
end
| uu____1021 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1039) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1045) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1078 -> (

let uu____1079 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1080 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1079 uu____1080)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1086 -> (match (b) with
| true -> begin
(

let uu____1087 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1088 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____1087 uu____1088)))
end
| uu____1089 -> begin
(

let uu____1090 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1091 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1090 uu____1091)))
end)));
b;
));
))


let is_type_binder : 'Auu____1098 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____1098)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1119 = (

let uu____1120 = (FStar_Syntax_Subst.compress t)
in uu____1120.FStar_Syntax_Syntax.n)
in (match (uu____1119) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1123; FStar_Syntax_Syntax.fv_delta = uu____1124; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1125; FStar_Syntax_Syntax.fv_delta = uu____1126; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1127))}) -> begin
true
end
| uu____1134 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1139 = (

let uu____1140 = (FStar_Syntax_Subst.compress t)
in uu____1140.FStar_Syntax_Syntax.n)
in (match (uu____1139) with
| FStar_Syntax_Syntax.Tm_constant (uu____1143) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1144) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1145) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1146) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1185 = (is_constructor head1)
in (match (uu____1185) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1201 -> (match (uu____1201) with
| (te, uu____1207) -> begin
(is_fstar_value te)
end))))
end
| uu____1208 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1210) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1216, uu____1217) -> begin
(is_fstar_value t1)
end
| uu____1258 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1263) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1264) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1265) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1266) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1277, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1286, fields) -> begin
(FStar_Util.for_all (fun uu____1311 -> (match (uu____1311) with
| (uu____1316, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1319) -> begin
(is_ml_value h)
end
| uu____1324 -> begin
false
end))


let fresh : Prims.string  ->  Prims.string = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1354 = (

let uu____1355 = (FStar_ST.op_Bang c)
in (FStar_Util.string_of_int uu____1355))
in (Prims.strcat x uu____1354));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1438 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1440 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1440) with
| true -> begin
(aux bs e' copt)
end
| uu____1441 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1446 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1446))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1524 -> begin
(

let uu____1525 = (FStar_List.hd l)
in (match (uu____1525) with
| (p1, w1, e1) -> begin
(

let uu____1559 = (

let uu____1568 = (FStar_List.tl l)
in (FStar_List.hd uu____1568))
in (match (uu____1559) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1642 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_GHOST) || ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1708 = (erasable g f ty)
in (match (uu____1708) with
| true -> begin
(

let uu____1709 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1709) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1710 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1711 -> begin
e
end))
in ((e1), (f), (ty))))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____1720 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1720) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____1735 -> begin
(

let vs = (FStar_List.map (fun uu____1740 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____1751 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____1765 -> (match (uu____1765) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____1751))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____1789 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____1791 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1791 (FStar_Pervasives_Native.Some ("Kremlin")))))
in (match (uu____1789) with
| true -> begin
e
end
| uu____1796 -> begin
(eta_expand expect e)
end)))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1814 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____1814) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____1824 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1836 -> (

let uu____1837 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1838 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1839 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1837 uu____1838 uu____1839))))));
(

let uu____1840 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))))
in (maybe_eta_expand expect uu____1840));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1849 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1849) with
| FStar_Util.Inl (uu____1850, t) -> begin
t
end
| uu____1864 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1907) -> begin
(

let uu____1914 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1914) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____1918 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1921 = (is_top_ty mlt)
in (match (uu____1921) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1923 -> begin
mlt
end))))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____1927) -> begin
(

let uu____1928 = (

let uu____1929 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1929))
in (failwith uu____1928))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1930) -> begin
(

let uu____1955 = (

let uu____1956 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1956))
in (failwith uu____1955))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____1957 = (

let uu____1958 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1958))
in (failwith uu____1957))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1959) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1960) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1978) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____1983; FStar_Syntax_Syntax.index = uu____1984; FStar_Syntax_Syntax.sort = t2}, uu____1986) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1994) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2000, uu____2001) -> begin
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

let uu____2068 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2068) with
| (bs1, c1) -> begin
(

let uu____2075 = (binders_as_ml_binders env bs1)
in (match (uu____2075) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2102 = (

let uu____2109 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____2109))
in (match (uu____2102) with
| (ed, qualifiers) -> begin
(

let uu____2130 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____2130) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____2135 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2137 = (FStar_List.fold_right (fun uu____2156 uu____2157 -> (match (((uu____2156), (uu____2157))) with
| ((uu____2178, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____2137) with
| (uu____2190, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____2215 = (

let uu____2216 = (FStar_Syntax_Util.un_uinst head1)
in uu____2216.FStar_Syntax_Syntax.n)
in (match (uu____2215) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____2243 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____2243))
end
| uu____2260 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2263) -> begin
(

let uu____2284 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____2284) with
| (bs1, ty1) -> begin
(

let uu____2291 = (binders_as_ml_binders env bs1)
in (match (uu____2291) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2316) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_let (uu____2317) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____2330) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____2354 -> (match (uu____2354) with
| (a, uu____2360) -> begin
(

let uu____2361 = (is_type g a)
in (match (uu____2361) with
| true -> begin
(term_as_mlty' g a)
end
| uu____2362 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____2366 = (

let uu____2379 = (FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2379) with
| ((uu____2400, fvty), uu____2402) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) g.FStar_Extraction_ML_UEnv.tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____2366) with
| (formals, uu____2409) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____2453 = (FStar_Util.first_N n_args formals)
in (match (uu____2453) with
| (uu____2480, rest) -> begin
(

let uu____2506 = (FStar_List.map (fun uu____2514 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____2506))
end))
end
| uu____2519 -> begin
mlargs
end))
in (

let nm = (

let uu____2521 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____2521) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____2539 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2582 b -> (match (uu____2582) with
| (ml_bs, env) -> begin
(

let uu____2622 = (is_type_binder g b)
in (match (uu____2622) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____2640 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____2640), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____2651 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____2654 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____2654) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____2678 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____2678), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____2539) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____2748) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____2751, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____2755 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| FStar_Pervasives_Native.Some ([], t) when (Prims.op_Equality t FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(match ((Prims.op_Equality body.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr)) with
| true -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____2785 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____2787 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____2788 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____2789 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____2792 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____2811 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____2811) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____2815 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____2842 -> begin
p
end)
end))
end
| uu____2845 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____2904 -> (

let uu____2905 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____2906 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____2905 uu____2906)))))
end
| uu____2907 -> begin
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

let uu____2946 = (

let uu____2947 = (

let uu____2954 = (

let uu____2957 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____2958 = (

let uu____2961 = (

let uu____2962 = (

let uu____2963 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_44 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_44)) uu____2963))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____2962))
in (uu____2961)::[])
in (uu____2957)::uu____2958))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____2954)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2947))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2946))
in (

let uu____2966 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____2966))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____2986 = (

let uu____2995 = (

let uu____3002 = (

let uu____3003 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____3003))
in ((uu____3002), ([])))
in FStar_Pervasives_Native.Some (uu____2995))
in (

let uu____3012 = (ok mlty)
in ((g), (uu____2986), (uu____3012))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3023 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3023) with
| (g1, x1) -> begin
(

let uu____3046 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3069 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3046)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3080 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3080) with
| (g1, x1) -> begin
(

let uu____3103 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3126 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3103)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____3135) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____3174 = (

let uu____3179 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____3179) with
| FStar_Util.Inr (uu____3184, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____3186; FStar_Extraction_ML_Syntax.loc = uu____3187}, ttys, uu____3189) -> begin
((n1), (ttys))
end
| uu____3202 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____3174) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____3224 = (FStar_Util.first_N nTyVars pats)
in (match (uu____3224) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___150_3324 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____3357 -> (match (uu____3357) with
| (p1, uu____3365) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____3370, t) -> begin
(term_as_mlty g t)
end
| uu____3376 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3380 -> (

let uu____3381 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____3381))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____3383 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____3383))))
end)) (fun uu___149_3397 -> (match (uu___149_3397) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____3412 = (FStar_Util.fold_map (fun g1 uu____3448 -> (match (uu____3448) with
| (p1, imp1) -> begin
(

let uu____3467 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None)
in (match (uu____3467) with
| (g2, p2, uu____3496) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____3412) with
| (g1, tyMLPats) -> begin
(

let uu____3557 = (FStar_Util.fold_map (fun uu____3621 uu____3622 -> (match (((uu____3621), (uu____3622))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____3715 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____3775 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____3715) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____3846 = (extract_one_pat false g2 p1 expected_ty)
in (match (uu____3846) with
| (g3, p2, uu____3887) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____3557) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____4005 = (

let uu____4016 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___146_4067 -> (match (uu___146_4067) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____4109 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4016 FStar_List.split))
in (match (uu____4005) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____4182 -> begin
false
end)
in (

let uu____4191 = (

let uu____4200 = (

let uu____4207 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____4210 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____4207), (uu____4210))))
in FStar_Pervasives_Native.Some (uu____4200))
in ((g2), (uu____4191), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____4301 = (extract_one_pat false g1 p1 expected_t1)
in (match (uu____4301) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____4358 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____4401 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____4401))
end))
in (

let uu____4402 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____4402) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____4544, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____4547 = (

let uu____4558 = (

let uu____4567 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____4567)))
in (uu____4558)::more_args)
in (eta_args uu____4547 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____4580, uu____4581) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____4604 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____4632, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____4664 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____4682 = (eta_args [] residualType)
in (match (uu____4682) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____4735 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____4735))
end
| uu____4736 -> begin
(

let uu____4747 = (FStar_List.unzip eargs)
in (match (uu____4747) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____4789 = (

let uu____4790 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____4790))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____4789))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____4799 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____4802, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4806; FStar_Extraction_ML_Syntax.loc = uu____4807}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____4834 -> begin
(

let uu____4837 = (

let uu____4844 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____4844), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4837))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4848; FStar_Extraction_ML_Syntax.loc = uu____4849}, uu____4850); FStar_Extraction_ML_Syntax.mlty = uu____4851; FStar_Extraction_ML_Syntax.loc = uu____4852}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____4883 -> begin
(

let uu____4886 = (

let uu____4893 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____4893), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4886))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4897; FStar_Extraction_ML_Syntax.loc = uu____4898}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____4906 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4906))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4910; FStar_Extraction_ML_Syntax.loc = uu____4911}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____4913))) -> begin
(

let uu____4926 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4926))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4930; FStar_Extraction_ML_Syntax.loc = uu____4931}, uu____4932); FStar_Extraction_ML_Syntax.mlty = uu____4933; FStar_Extraction_ML_Syntax.loc = uu____4934}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____4946 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4946))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4950; FStar_Extraction_ML_Syntax.loc = uu____4951}, uu____4952); FStar_Extraction_ML_Syntax.mlty = uu____4953; FStar_Extraction_ML_Syntax.loc = uu____4954}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____4956))) -> begin
(

let uu____4973 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4973))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____4979 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4979))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____4983))) -> begin
(

let uu____4992 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4992))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4996; FStar_Extraction_ML_Syntax.loc = uu____4997}, uu____4998), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5005 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5005))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5009; FStar_Extraction_ML_Syntax.loc = uu____5010}, uu____5011), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5012))) -> begin
(

let uu____5025 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5025))
end
| uu____5028 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____5047 = ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____5047) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____5048 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____5101 = (term_as_mlexpr' g t)
in (match (uu____5101) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5122 = (

let uu____5123 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5124 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5125 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____5123 uu____5124 uu____5125 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____5122))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____5134 = (check_term_as_mlexpr' g t f ty)
in (match (uu____5134) with
| (e, t1) -> begin
(

let uu____5145 = (erase g e t1 f)
in (match (uu____5145) with
| (r, uu____5157, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____5167 = (term_as_mlexpr g e0)
in (match (uu____5167) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____5186 = (maybe_coerce g e t ty)
in ((uu____5186), (ty)))
end
| uu____5187 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5204 = (

let uu____5205 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5206 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____5207 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____5205 uu____5206 uu____5207))))
in (FStar_Util.print_string uu____5204))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5215 = (

let uu____5216 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5216))
in (failwith uu____5215))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5223) -> begin
(

let uu____5248 = (

let uu____5249 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5249))
in (failwith uu____5248))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5256) -> begin
(

let uu____5273 = (

let uu____5274 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5274))
in (failwith uu____5273))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5281) -> begin
(

let uu____5282 = (

let uu____5283 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5283))
in (failwith uu____5282))
end
| FStar_Syntax_Syntax.Tm_type (uu____5290) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5291) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5298) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____5316 = (term_as_mlexpr' g t1)
in (match (uu____5316) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____5362 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____5377)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____5407 = (

let uu____5414 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____5414))
in (match (uu____5407) with
| (ed, qualifiers) -> begin
(

let uu____5441 = (

let uu____5442 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____5442 Prims.op_Negation))
in (match (uu____5441) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____5451 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____5458 -> begin
(term_as_mlexpr' g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5460) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5466) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____5472 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____5472) with
| (uu____5485, ty, uu____5487) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____5489 = (

let uu____5490 = (

let uu____5491 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_45 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_45)) uu____5491))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5490))
in ((uu____5489), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____5492) -> begin
(

let uu____5493 = (is_type g t)
in (match (uu____5493) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5500 -> begin
(

let uu____5501 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5501) with
| (FStar_Util.Inl (uu____5514), uu____5515) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____5552, x, mltys, uu____5555), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____5601 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____5601), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____5602 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5609) -> begin
(

let uu____5610 = (is_type g t)
in (match (uu____5610) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5617 -> begin
(

let uu____5618 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5618) with
| (FStar_Util.Inl (uu____5631), uu____5632) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____5669, x, mltys, uu____5672), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____5718 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____5718), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____5719 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____5749 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____5749) with
| (bs1, body1) -> begin
(

let uu____5762 = (binders_as_ml_binders g bs1)
in (match (uu____5762) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5795 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____5795) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____5796 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____5800 -> (

let uu____5801 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____5801))));
body1;
)
end)
in (

let uu____5802 = (term_as_mlexpr env body2)
in (match (uu____5802) with
| (ml_body, f, t1) -> begin
(

let uu____5818 = (FStar_List.fold_right (fun uu____5837 uu____5838 -> (match (((uu____5837), (uu____5838))) with
| ((uu____5859, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____5818) with
| (f1, tfun) -> begin
(

let uu____5879 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____5879), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____5886)); FStar_Syntax_Syntax.pos = uu____5887; FStar_Syntax_Syntax.vars = uu____5888}, uu____5889) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____5917)::((v1, uu____5919))::[]) when ((FStar_Syntax_Util.is_fstar_tactics_embed head1) && false) -> begin
(

let uu____5960 = (

let uu____5963 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.format2 "Trying to extract a quotation of %s" uu____5963))
in (

let s = (

let uu____5965 = (

let uu____5966 = (

let uu____5967 = (

let uu____5970 = (FStar_Util.marshal v1)
in (FStar_Util.bytes_of_string uu____5970))
in FStar_Extraction_ML_Syntax.MLC_Bytes (uu____5967))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____5966))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty uu____5965))
in (

let zero1 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int ((("0"), (FStar_Pervasives_Native.None))))))
in (

let term_ty = (

let uu____5985 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.fstar_syntax_syntax_term FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (term_as_mlty g uu____5985))
in (

let marshal_from_string = (

let string_to_term_ty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_string_ty), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty)))
in (FStar_Extraction_ML_Syntax.with_ty string_to_term_ty (FStar_Extraction_ML_Syntax.MLE_Name (((("Marshal")::[]), ("from_string"))))))
in (

let uu____5990 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty) (FStar_Extraction_ML_Syntax.MLE_App (((marshal_from_string), ((s)::(zero1)::[])))))
in ((uu____5990), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty))))))))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___147_6022 -> (match (uu___147_6022) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6023 -> begin
false
end))))))
in (

let uu____6024 = (

let uu____6029 = (

let uu____6030 = (FStar_Syntax_Subst.compress head1)
in uu____6030.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____6029)))
in (match (uu____6024) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6039), uu____6040) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6058, FStar_Syntax_Syntax.Tm_abs (bs, uu____6060, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6081, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____6083 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6083))
in (

let tm = (

let uu____6093 = (

let uu____6094 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____6095 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6094 uu____6095)))
in (uu____6093 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr' g tm)))
end
| uu____6104 -> begin
(

let rec extract_app = (fun is_data uu____6149 uu____6150 restArgs -> (match (((uu____6149), (uu____6150))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____6240) -> begin
(

let evaluation_order_guaranteed = (((Prims.op_Equality (FStar_List.length mlargs_f) (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____6262 -> begin
false
end))
in (

let uu____6263 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____6288 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (([]), (uu____6288)))
end
| uu____6319 -> begin
(FStar_List.fold_left (fun uu____6342 uu____6343 -> (match (((uu____6342), (uu____6343))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((Prims.op_Equality f1 FStar_Extraction_ML_Syntax.E_PURE) || (Prims.op_Equality f1 FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____6444 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____6446 = (

let uu____6449 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____6449)::out_args)
in (((((x), (arg)))::lbs), (uu____6446))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____6263) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____6499 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____6499))
in (

let l_app = (FStar_List.fold_right (fun uu____6511 out -> (match (uu____6511) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____6532))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____6563 = (

let uu____6568 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____6568), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____6563 rest))
end
| (((e0, uu____6580))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____6612 = (term_as_mlexpr g e0)
in (match (uu____6612) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____6629 = (

let uu____6634 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____6634), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____6629 rest)))
end)))
end
| uu____6645 -> begin
(

let uu____6658 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____6658) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____6715 args1 -> (match (uu____6715) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____6747)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6825))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____6827, f', t3)) -> begin
(

let uu____6864 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____6864 t3))
end
| uu____6865 -> begin
((args2), (f1), (t2))
end))
in (

let uu____6890 = (remove_implicits args1 f t1)
in (match (uu____6890) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____6946 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____6959 = (is_type g t)
in (match (uu____6959) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____6966 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid) && (

let uu____6976 = (

let uu____6977 = (FStar_Extraction_ML_Syntax.string_of_mlpath g.FStar_Extraction_ML_UEnv.currentModule)
in (Prims.op_Equality uu____6977 "FStar.Tactics.Builtins"))
in (not (uu____6976)))) -> begin
(match (args) with
| (a)::(b)::[] -> begin
(term_as_mlexpr g (FStar_Pervasives_Native.fst a))
end
| uu____7018 -> begin
(

let uu____7027 = (FStar_Syntax_Print.args_to_string args)
in (failwith uu____7027))
end)
end
| FStar_Syntax_Syntax.Tm_name (uu____7034) -> begin
(

let uu____7035 = (

let uu____7048 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7048) with
| (FStar_Util.Inr (uu____7067, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7112 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7035) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7162))::uu____7163 -> begin
(is_type g a)
end
| uu____7182 -> begin
false
end)
in (

let uu____7191 = (match (vars) with
| (uu____7220)::uu____7221 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7232 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7260 = (FStar_Util.first_N n1 args)
in (match (uu____7260) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7349 -> (match (uu____7349) with
| (x, uu____7355) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____7368 -> begin
(

let uu___151_7371 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___151_7371.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___151_7371.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7375) -> begin
(

let uu___152_7376 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___152_7376.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___152_7376.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7377) -> begin
(

let uu___152_7378 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___152_7378.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___152_7378.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7380; FStar_Extraction_ML_Syntax.loc = uu____7381})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___153_7387 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___153_7387.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___153_7387.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7388 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____7397 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7191) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7449 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7449), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7450 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7459) -> begin
(

let uu____7460 = (

let uu____7473 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7473) with
| (FStar_Util.Inr (uu____7492, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7537 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7460) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7587))::uu____7588 -> begin
(is_type g a)
end
| uu____7607 -> begin
false
end)
in (

let uu____7616 = (match (vars) with
| (uu____7645)::uu____7646 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7657 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7685 = (FStar_Util.first_N n1 args)
in (match (uu____7685) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7774 -> (match (uu____7774) with
| (x, uu____7780) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____7793 -> begin
(

let uu___151_7796 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___151_7796.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___151_7796.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7800) -> begin
(

let uu___152_7801 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___152_7801.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___152_7801.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7802) -> begin
(

let uu___152_7803 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___152_7803.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___152_7803.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7805; FStar_Extraction_ML_Syntax.loc = uu____7806})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___153_7812 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___153_7812.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___153_7812.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7813 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____7822 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7616) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7874 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7874), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7875 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____7884 -> begin
(

let uu____7885 = (term_as_mlexpr g head2)
in (match (uu____7885) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____7903), f) -> begin
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

let uu____7970 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____7970) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____8001 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____8014 -> begin
(

let uu____8015 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____8015) with
| true -> begin
((lbs), (e'))
end
| uu____8026 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____8029 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____8029))
in (

let lb1 = (

let uu___154_8031 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___154_8031.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___154_8031.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___154_8031.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___154_8031.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____8001) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____8063 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____8063))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____8070 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____8074 = (FStar_Options.ml_ish ())
in (match (uu____8074) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____8077 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___155_8078 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_8078.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___155_8078.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___155_8078.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___155_8078.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____8079 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____8101 -> (match (uu____8101) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____8121; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____8191 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____8191 (is_type_binder g))) -> begin
(

let uu____8204 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8204) with
| (bs1, c1) -> begin
(

let uu____8229 = (

let uu____8236 = (FStar_Util.prefix_until (fun x -> (

let uu____8272 = (is_type_binder g x)
in (not (uu____8272)))) bs1)
in (match (uu____8236) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____8360 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____8360)))
end))
in (match (uu____8229) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____8405 = (normalize_abs e)
in (FStar_All.pipe_right uu____8405 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____8447 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____8447) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____8500 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____8500) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____8588 uu____8589 -> (match (((uu____8588), (uu____8589))) with
| ((x, uu____8607), (y, uu____8609)) -> begin
(

let uu____8618 = (

let uu____8625 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____8625)))
in FStar_Syntax_Syntax.NT (uu____8618))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____8636 -> (match (uu____8636) with
| (a, uu____8642) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____8651 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____8669 -> (match (uu____8669) with
| (x, uu____8675) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8651), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____8683 = (is_fstar_value body1)
in (not (uu____8683)))
end
| uu____8684 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____8696 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____8698 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((t2), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____8734 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____8753) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8770 -> (match (uu____8770) with
| (a, uu____8776) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8785 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8797 -> (match (uu____8797) with
| (x, uu____8803) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8785), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8819 -> (match (uu____8819) with
| (bv, uu____8825) -> begin
(

let uu____8826 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8826 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8868) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8879 -> (match (uu____8879) with
| (a, uu____8885) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8894 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8906 -> (match (uu____8906) with
| (x, uu____8912) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8894), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8928 -> (match (uu____8928) with
| (bv, uu____8934) -> begin
(

let uu____8935 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8935 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____8977) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8988 -> (match (uu____8988) with
| (a, uu____8994) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9003 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9015 -> (match (uu____9015) with
| (x, uu____9021) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9003), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9037 -> (match (uu____9037) with
| (bv, uu____9043) -> begin
(

let uu____9044 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9044 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____9086 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____9105 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____9209 -> (match (uu____9209) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____9344 -> (match (uu____9344) with
| (a, uu____9350) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____9352 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____9352) with
| (e1, uu____9362) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____9429 = (FStar_List.fold_right (fun lb uu____9520 -> (match (uu____9520) with
| (env, lbs4) -> begin
(

let uu____9645 = lb
in (match (uu____9645) with
| (lbname, uu____9693, (t1, (uu____9695, polytype)), add_unit, uu____9698) -> begin
(

let uu____9711 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____9711) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____9429) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____9913 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____9988 = (term_as_mlexpr env_body e'1)
in (match (uu____9988) with
| (e'2, f', t') -> begin
(

let f = (

let uu____10005 = (

let uu____10008 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____10008)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____10005))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____10016 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____10017 = (

let uu____10018 = (

let uu____10019 = (

let uu____10020 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), ([]), (uu____10020)))
in (mk_MLE_Let top_level uu____10019 e'2))
in (

let uu____10031 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____10018 uu____10031)))
in ((uu____10017), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____10070 = (term_as_mlexpr g scrutinee)
in (match (uu____10070) with
| (e, f_e, t_e) -> begin
(

let uu____10086 = (check_pats_for_ite pats)
in (match (uu____10086) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____10143 = (term_as_mlexpr g then_e1)
in (match (uu____10143) with
| (then_mle, f_then, t_then) -> begin
(

let uu____10159 = (term_as_mlexpr g else_e1)
in (match (uu____10159) with
| (else_mle, f_else, t_else) -> begin
(

let uu____10175 = (

let uu____10184 = (type_leq g t_then t_else)
in (match (uu____10184) with
| true -> begin
((t_else), (no_lift))
end
| uu____10197 -> begin
(

let uu____10198 = (type_leq g t_else t_then)
in (match (uu____10198) with
| true -> begin
((t_then), (no_lift))
end
| uu____10211 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____10175) with
| (t_branch, maybe_lift1) -> begin
(

let uu____10232 = (

let uu____10233 = (

let uu____10234 = (

let uu____10243 = (maybe_lift1 then_mle t_then)
in (

let uu____10244 = (

let uu____10247 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____10247))
in ((e), (uu____10243), (uu____10244))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____10234))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____10233))
in (

let uu____10250 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____10232), (uu____10250), (t_branch))))
end))
end))
end))
end
| uu____10251 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____10266 -> begin
(

let uu____10267 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____10376 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____10376) with
| (pat, when_opt, branch1) -> begin
(

let uu____10420 = (extract_pat g pat t_e)
in (match (uu____10420) with
| (env, p, pat_t_compat) -> begin
(

let uu____10478 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____10500 = (term_as_mlexpr env w)
in (match (uu____10500) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end))
end)
in (match (uu____10478) with
| (when_opt1, f_when) -> begin
(

let uu____10549 = (term_as_mlexpr env branch1)
in (match (uu____10549) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____10583 = (FStar_All.pipe_right p (FStar_List.map (fun uu____10660 -> (match (uu____10660) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____10583)))
end))
end))
end))
end))) true))
in (match (uu____10267) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____10820 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____10825 -> (

let uu____10826 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____10827 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____10826 uu____10827)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____10852 = (

let uu____10861 = (

let uu____10878 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____10878))
in (FStar_All.pipe_left FStar_Util.right uu____10861))
in (match (uu____10852) with
| (uu____10921, fw, uu____10923, uu____10924) -> begin
(

let uu____10925 = (

let uu____10926 = (

let uu____10927 = (

let uu____10934 = (

let uu____10937 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____10937)::[])
in ((fw), (uu____10934)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____10927))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____10926))
in ((uu____10925), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____10940, uu____10941, (uu____10942, f_first, t_first)))::rest -> begin
(

let uu____11002 = (FStar_List.fold_left (fun uu____11044 uu____11045 -> (match (((uu____11044), (uu____11045))) with
| ((topt, f), (uu____11102, uu____11103, (uu____11104, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____11160 = (type_leq g t1 t_branch)
in (match (uu____11160) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____11163 -> begin
(

let uu____11164 = (type_leq g t_branch t1)
in (match (uu____11164) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____11167 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____11002) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____11259 -> (match (uu____11259) with
| (p, (wopt, uu____11288), (b1, uu____11290, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____11309) -> begin
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

let uu____11314 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____11314), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____11337 = (

let uu____11342 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11342))
in (match (uu____11337) with
| (uu____11367, fstar_disc_type) -> begin
(

let wildcards = (

let uu____11376 = (

let uu____11377 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____11377.FStar_Syntax_Syntax.n)
in (match (uu____11376) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11387) -> begin
(

let uu____11404 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___148_11436 -> (match (uu___148_11436) with
| (uu____11443, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11444))) -> begin
true
end
| uu____11447 -> begin
false
end))))
in (FStar_All.pipe_right uu____11404 (FStar_List.map (fun uu____11480 -> (

let uu____11487 = (fresh "_")
in ((uu____11487), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____11488 -> begin
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

let uu____11499 = (

let uu____11500 = (

let uu____11511 = (

let uu____11512 = (

let uu____11513 = (

let uu____11528 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____11531 = (

let uu____11542 = (

let uu____11551 = (

let uu____11552 = (

let uu____11559 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____11559), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____11552))
in (

let uu____11562 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____11551), (FStar_Pervasives_Native.None), (uu____11562))))
in (

let uu____11565 = (

let uu____11576 = (

let uu____11585 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____11585)))
in (uu____11576)::[])
in (uu____11542)::uu____11565))
in ((uu____11528), (uu____11531))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____11513))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11512))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____11511)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____11500))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11499))
in (

let uu____11640 = (

let uu____11641 = (

let uu____11644 = (

let uu____11645 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____11645; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____11644)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____11641)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____11640)))))))
end)))




