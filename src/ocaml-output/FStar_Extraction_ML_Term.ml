
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
| uu____1474 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1476 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1476) with
| true -> begin
(aux bs e' copt)
end
| uu____1477 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1482 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1482))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match ((Prims.op_disEquality (FStar_List.length l) (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1560 -> begin
(

let uu____1561 = (FStar_List.hd l)
in (match (uu____1561) with
| (p1, w1, e1) -> begin
(

let uu____1595 = (

let uu____1604 = (FStar_List.tl l)
in (FStar_List.hd uu____1604))
in (match (uu____1595) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1678 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_GHOST) || ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1744 = (erasable g f ty)
in (match (uu____1744) with
| true -> begin
(

let uu____1745 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1745) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1746 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1747 -> begin
e
end))
in ((e1), (f), (ty))))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____1756 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1756) with
| (ts, r) -> begin
(match ((Prims.op_Equality ts [])) with
| true -> begin
e
end
| uu____1771 -> begin
(

let vs = (FStar_List.map (fun uu____1776 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____1787 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____1801 -> (match (uu____1801) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____1787))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____1825 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____1827 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1827 (FStar_Pervasives_Native.Some ("Kremlin")))))
in (match (uu____1825) with
| true -> begin
e
end
| uu____1832 -> begin
(eta_expand expect e)
end)))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1850 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____1850) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____1860 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1872 -> (

let uu____1873 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1874 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1875 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1873 uu____1874 uu____1875))))));
(

let uu____1876 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))))
in (maybe_eta_expand expect uu____1876));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1885 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1885) with
| FStar_Util.Inl (uu____1886, t) -> begin
t
end
| uu____1900 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1943) -> begin
(

let uu____1950 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1950) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____1954 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1957 = (is_top_ty mlt)
in (match (uu____1957) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1959 -> begin
mlt
end))))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____1963) -> begin
(

let uu____1964 = (

let uu____1965 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1965))
in (failwith uu____1964))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1966) -> begin
(

let uu____1991 = (

let uu____1992 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1992))
in (failwith uu____1991))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____1993 = (

let uu____1994 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1994))
in (failwith uu____1993))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1995) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1996) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____2014) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____2019; FStar_Syntax_Syntax.index = uu____2020; FStar_Syntax_Syntax.sort = t2}, uu____2022) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2030) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2036, uu____2037) -> begin
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

let uu____2104 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2104) with
| (bs1, c1) -> begin
(

let uu____2111 = (binders_as_ml_binders env bs1)
in (match (uu____2111) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2138 = (

let uu____2145 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____2145))
in (match (uu____2138) with
| (ed, qualifiers) -> begin
(

let uu____2166 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____2166) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____2171 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2173 = (FStar_List.fold_right (fun uu____2192 uu____2193 -> (match (((uu____2192), (uu____2193))) with
| ((uu____2214, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____2173) with
| (uu____2226, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____2251 = (

let uu____2252 = (FStar_Syntax_Util.un_uinst head1)
in uu____2252.FStar_Syntax_Syntax.n)
in (match (uu____2251) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____2279 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____2279))
end
| uu____2296 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2299) -> begin
(

let uu____2320 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____2320) with
| (bs1, ty1) -> begin
(

let uu____2327 = (binders_as_ml_binders env bs1)
in (match (uu____2327) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2352) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_let (uu____2353) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____2366) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____2390 -> (match (uu____2390) with
| (a, uu____2396) -> begin
(

let uu____2397 = (is_type g a)
in (match (uu____2397) with
| true -> begin
(term_as_mlty' g a)
end
| uu____2398 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____2402 = (

let uu____2415 = (FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2415) with
| ((uu____2436, fvty), uu____2438) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) g.FStar_Extraction_ML_UEnv.tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____2402) with
| (formals, uu____2445) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____2489 = (FStar_Util.first_N n_args formals)
in (match (uu____2489) with
| (uu____2516, rest) -> begin
(

let uu____2542 = (FStar_List.map (fun uu____2550 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____2542))
end))
end
| uu____2555 -> begin
mlargs
end))
in (

let nm = (

let uu____2557 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____2557) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____2575 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2618 b -> (match (uu____2618) with
| (ml_bs, env) -> begin
(

let uu____2658 = (is_type_binder g b)
in (match (uu____2658) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____2676 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____2676), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____2687 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____2690 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____2690) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____2714 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____2714), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____2575) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____2784) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____2787, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____2791 -> begin
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
| uu____2821 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (Prims.op_Equality x lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____2823 when (Prims.op_Equality lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____2824 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____2825 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____2828 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____2847 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____2847) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____2851 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____2878 -> begin
p
end)
end))
end
| uu____2881 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____2940 -> (

let uu____2941 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____2942 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____2941 uu____2942)))))
end
| uu____2943 -> begin
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

let uu____2982 = (

let uu____2983 = (

let uu____2990 = (

let uu____2993 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____2994 = (

let uu____2997 = (

let uu____2998 = (

let uu____2999 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_44 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_44)) uu____2999))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____2998))
in (uu____2997)::[])
in (uu____2993)::uu____2994))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____2990)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2983))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____2982))
in (

let uu____3002 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____3002))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____3022 = (

let uu____3031 = (

let uu____3038 = (

let uu____3039 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____3039))
in ((uu____3038), ([])))
in FStar_Pervasives_Native.Some (uu____3031))
in (

let uu____3048 = (ok mlty)
in ((g), (uu____3022), (uu____3048))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3059 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3059) with
| (g1, x1) -> begin
(

let uu____3082 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3105 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3082)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3116 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3116) with
| (g1, x1) -> begin
(

let uu____3139 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3162 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3139)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____3171) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____3210 = (

let uu____3215 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____3215) with
| FStar_Util.Inr (uu____3220, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____3222; FStar_Extraction_ML_Syntax.loc = uu____3223}, ttys, uu____3225) -> begin
((n1), (ttys))
end
| uu____3238 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____3210) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____3260 = (FStar_Util.first_N nTyVars pats)
in (match (uu____3260) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = (FStar_All.try_with (fun uu___172_3360 -> (match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____3393 -> (match (uu____3393) with
| (p1, uu____3401) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____3406, t) -> begin
(term_as_mlty g t)
end
| uu____3412 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3416 -> (

let uu____3417 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____3417))));
(FStar_Exn.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____3419 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____3419))))
end)) (fun uu___171_3433 -> (match (uu___171_3433) with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____3448 = (FStar_Util.fold_map (fun g1 uu____3484 -> (match (uu____3484) with
| (p1, imp1) -> begin
(

let uu____3503 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None)
in (match (uu____3503) with
| (g2, p2, uu____3532) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____3448) with
| (g1, tyMLPats) -> begin
(

let uu____3593 = (FStar_Util.fold_map (fun uu____3657 uu____3658 -> (match (((uu____3657), (uu____3658))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____3751 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____3811 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____3751) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____3882 = (extract_one_pat false g2 p1 expected_ty)
in (match (uu____3882) with
| (g3, p2, uu____3923) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____3593) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____4041 = (

let uu____4052 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___168_4103 -> (match (uu___168_4103) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____4145 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4052 FStar_List.split))
in (match (uu____4041) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____4218 -> begin
false
end)
in (

let uu____4227 = (

let uu____4236 = (

let uu____4243 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____4246 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____4243), (uu____4246))))
in FStar_Pervasives_Native.Some (uu____4236))
in ((g2), (uu____4227), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____4337 = (extract_one_pat false g1 p1 expected_t1)
in (match (uu____4337) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____4394 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____4437 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____4437))
end))
in (

let uu____4438 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____4438) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____4580, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____4583 = (

let uu____4594 = (

let uu____4603 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____4603)))
in (uu____4594)::more_args)
in (eta_args uu____4583 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____4616, uu____4617) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____4640 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____4668, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____4700 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____4718 = (eta_args [] residualType)
in (match (uu____4718) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____4771 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____4771))
end
| uu____4772 -> begin
(

let uu____4783 = (FStar_List.unzip eargs)
in (match (uu____4783) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____4825 = (

let uu____4826 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____4826))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____4825))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____4835 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____4838, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4842; FStar_Extraction_ML_Syntax.loc = uu____4843}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____4870 -> begin
(

let uu____4873 = (

let uu____4880 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____4880), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4873))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4884; FStar_Extraction_ML_Syntax.loc = uu____4885}, uu____4886); FStar_Extraction_ML_Syntax.mlty = uu____4887; FStar_Extraction_ML_Syntax.loc = uu____4888}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____4919 -> begin
(

let uu____4922 = (

let uu____4929 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____4929), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4922))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4933; FStar_Extraction_ML_Syntax.loc = uu____4934}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____4942 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4942))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4946; FStar_Extraction_ML_Syntax.loc = uu____4947}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____4949))) -> begin
(

let uu____4962 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4962))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4966; FStar_Extraction_ML_Syntax.loc = uu____4967}, uu____4968); FStar_Extraction_ML_Syntax.mlty = uu____4969; FStar_Extraction_ML_Syntax.loc = uu____4970}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____4982 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4982))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4986; FStar_Extraction_ML_Syntax.loc = uu____4987}, uu____4988); FStar_Extraction_ML_Syntax.mlty = uu____4989; FStar_Extraction_ML_Syntax.loc = uu____4990}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____4992))) -> begin
(

let uu____5009 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5009))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5015 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5015))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5019))) -> begin
(

let uu____5028 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5028))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5032; FStar_Extraction_ML_Syntax.loc = uu____5033}, uu____5034), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5041 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5041))
end
| (FStar_Extraction_ML_Syntax.MLE_TApp ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____5045; FStar_Extraction_ML_Syntax.loc = uu____5046}, uu____5047), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5048))) -> begin
(

let uu____5061 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5061))
end
| uu____5064 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____5083 = ((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____5083) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____5084 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____5137 = (term_as_mlexpr' g t)
in (match (uu____5137) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5158 = (

let uu____5159 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5160 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5161 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____5159 uu____5160 uu____5161 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____5158))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____5170 = (check_term_as_mlexpr' g t f ty)
in (match (uu____5170) with
| (e, t1) -> begin
(

let uu____5181 = (erase g e t1 f)
in (match (uu____5181) with
| (r, uu____5193, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____5203 = (term_as_mlexpr g e0)
in (match (uu____5203) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____5222 = (maybe_coerce g e t ty)
in ((uu____5222), (ty)))
end
| uu____5223 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5240 = (

let uu____5241 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5242 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____5243 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____5241 uu____5242 uu____5243))))
in (FStar_Util.print_string uu____5240))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5251 = (

let uu____5252 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5252))
in (failwith uu____5251))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5259) -> begin
(

let uu____5284 = (

let uu____5285 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5285))
in (failwith uu____5284))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5292) -> begin
(

let uu____5309 = (

let uu____5310 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5310))
in (failwith uu____5309))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5317) -> begin
(

let uu____5318 = (

let uu____5319 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5319))
in (failwith uu____5318))
end
| FStar_Syntax_Syntax.Tm_type (uu____5326) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5327) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5334) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____5352 = (term_as_mlexpr' g t1)
in (match (uu____5352) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____5398 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____5413)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____5443 = (

let uu____5450 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____5450))
in (match (uu____5443) with
| (ed, qualifiers) -> begin
(

let uu____5477 = (

let uu____5478 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____5478 Prims.op_Negation))
in (match (uu____5477) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____5487 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____5494 -> begin
(term_as_mlexpr' g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5496) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5502) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____5508 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____5508) with
| (uu____5521, ty, uu____5523) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____5525 = (

let uu____5526 = (

let uu____5527 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_45 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_45)) uu____5527))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5526))
in ((uu____5525), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____5528) -> begin
(

let uu____5529 = (is_type g t)
in (match (uu____5529) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5536 -> begin
(

let uu____5537 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5537) with
| (FStar_Util.Inl (uu____5550), uu____5551) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____5588, x, mltys, uu____5591), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____5637 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____5637), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____5638 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5645) -> begin
(

let uu____5646 = (is_type g t)
in (match (uu____5646) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5653 -> begin
(

let uu____5654 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5654) with
| (FStar_Util.Inl (uu____5667), uu____5668) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____5705, x, mltys, uu____5708), qual) -> begin
(match (mltys) with
| ([], t1) when (Prims.op_Equality t1 FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____5754 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____5754), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____5755 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____5785 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____5785) with
| (bs1, body1) -> begin
(

let uu____5798 = (binders_as_ml_binders g bs1)
in (match (uu____5798) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5831 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____5831) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____5832 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____5836 -> (

let uu____5837 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____5837))));
body1;
)
end)
in (

let uu____5838 = (term_as_mlexpr env body2)
in (match (uu____5838) with
| (ml_body, f, t1) -> begin
(

let uu____5854 = (FStar_List.fold_right (fun uu____5873 uu____5874 -> (match (((uu____5873), (uu____5874))) with
| ((uu____5895, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____5854) with
| (f1, tfun) -> begin
(

let uu____5915 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____5915), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____5922)); FStar_Syntax_Syntax.pos = uu____5923; FStar_Syntax_Syntax.vars = uu____5924}, uu____5925) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____5953)::((v1, uu____5955))::[]) when ((FStar_Syntax_Util.is_fstar_tactics_embed head1) && false) -> begin
(

let uu____5996 = (

let uu____5999 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.format2 "Trying to extract a quotation of %s" uu____5999))
in (

let s = (

let uu____6001 = (

let uu____6002 = (

let uu____6003 = (

let uu____6006 = (FStar_Util.marshal v1)
in (FStar_Util.bytes_of_string uu____6006))
in FStar_Extraction_ML_Syntax.MLC_Bytes (uu____6003))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____6002))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty uu____6001))
in (

let zero1 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int ((("0"), (FStar_Pervasives_Native.None))))))
in (

let term_ty = (

let uu____6021 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.fstar_syntax_syntax_term FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (term_as_mlty g uu____6021))
in (

let marshal_from_string = (

let string_to_term_ty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_string_ty), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty)))
in (FStar_Extraction_ML_Syntax.with_ty string_to_term_ty (FStar_Extraction_ML_Syntax.MLE_Name (((("Marshal")::[]), ("from_string"))))))
in (

let uu____6026 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty) (FStar_Extraction_ML_Syntax.MLE_App (((marshal_from_string), ((s)::(zero1)::[])))))
in ((uu____6026), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty))))))))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___169_6058 -> (match (uu___169_6058) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6059 -> begin
false
end))))))
in (

let uu____6060 = (

let uu____6065 = (

let uu____6066 = (FStar_Syntax_Subst.compress head1)
in uu____6066.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____6065)))
in (match (uu____6060) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6075), uu____6076) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6094, FStar_Syntax_Syntax.Tm_abs (bs, uu____6096, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6117, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____6119 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6119))
in (

let tm = (

let uu____6129 = (

let uu____6130 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____6131 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6130 uu____6131)))
in (uu____6129 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr' g tm)))
end
| uu____6140 -> begin
(

let rec extract_app = (fun is_data uu____6185 uu____6186 restArgs -> (match (((uu____6185), (uu____6186))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____6276) -> begin
(

let evaluation_order_guaranteed = (((Prims.op_Equality (FStar_List.length mlargs_f) (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____6298 -> begin
false
end))
in (

let uu____6299 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____6324 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (([]), (uu____6324)))
end
| uu____6355 -> begin
(FStar_List.fold_left (fun uu____6378 uu____6379 -> (match (((uu____6378), (uu____6379))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((Prims.op_Equality f1 FStar_Extraction_ML_Syntax.E_PURE) || (Prims.op_Equality f1 FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____6480 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____6482 = (

let uu____6485 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____6485)::out_args)
in (((((x), (arg)))::lbs), (uu____6482))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____6299) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____6535 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____6535))
in (

let l_app = (FStar_List.fold_right (fun uu____6547 out -> (match (uu____6547) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____6568))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____6599 = (

let uu____6604 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____6604), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____6599 rest))
end
| (((e0, uu____6616))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____6648 = (term_as_mlexpr g e0)
in (match (uu____6648) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____6665 = (

let uu____6670 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____6670), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____6665 rest)))
end)))
end
| uu____6681 -> begin
(

let uu____6694 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____6694) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____6751 args1 -> (match (uu____6751) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____6783)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6861))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____6863, f', t3)) -> begin
(

let uu____6900 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____6900 t3))
end
| uu____6901 -> begin
((args2), (f1), (t2))
end))
in (

let uu____6926 = (remove_implicits args1 f t1)
in (match (uu____6926) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____6982 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____6995 = (is_type g t)
in (match (uu____6995) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____7002 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid) && (

let uu____7012 = (

let uu____7013 = (FStar_Extraction_ML_Syntax.string_of_mlpath g.FStar_Extraction_ML_UEnv.currentModule)
in (Prims.op_Equality uu____7013 "FStar.Tactics.Builtins"))
in (not (uu____7012)))) -> begin
(match (args) with
| (a)::(b)::[] -> begin
(term_as_mlexpr g (FStar_Pervasives_Native.fst a))
end
| uu____7054 -> begin
(

let uu____7063 = (FStar_Syntax_Print.args_to_string args)
in (failwith uu____7063))
end)
end
| FStar_Syntax_Syntax.Tm_name (uu____7070) -> begin
(

let uu____7071 = (

let uu____7084 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7084) with
| (FStar_Util.Inr (uu____7103, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7148 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7071) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7198))::uu____7199 -> begin
(is_type g a)
end
| uu____7218 -> begin
false
end)
in (

let uu____7227 = (match (vars) with
| (uu____7256)::uu____7257 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7268 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7296 = (FStar_Util.first_N n1 args)
in (match (uu____7296) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7385 -> (match (uu____7385) with
| (x, uu____7391) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____7404 -> begin
(

let uu___173_7407 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___173_7407.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___173_7407.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7411) -> begin
(

let uu___174_7412 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___174_7412.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___174_7412.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7413) -> begin
(

let uu___174_7414 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___174_7414.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___174_7414.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7416; FStar_Extraction_ML_Syntax.loc = uu____7417})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___175_7423 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___175_7423.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___175_7423.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7424 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____7433 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7227) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7485 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7485), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7486 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7495) -> begin
(

let uu____7496 = (

let uu____7509 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7509) with
| (FStar_Util.Inr (uu____7528, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7573 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7496) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7623))::uu____7624 -> begin
(is_type g a)
end
| uu____7643 -> begin
false
end)
in (

let uu____7652 = (match (vars) with
| (uu____7681)::uu____7682 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7693 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7721 = (FStar_Util.first_N n1 args)
in (match (uu____7721) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7810 -> (match (uu____7810) with
| (x, uu____7816) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let mk_tapp = (fun e ty_args -> (match (ty_args) with
| [] -> begin
e
end
| uu____7829 -> begin
(

let uu___173_7832 = e
in {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_TApp (((e), (ty_args))); FStar_Extraction_ML_Syntax.mlty = uu___173_7832.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = uu___173_7832.FStar_Extraction_ML_Syntax.loc})
end))
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7836) -> begin
(

let uu___174_7837 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___174_7837.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___174_7837.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7838) -> begin
(

let uu___174_7839 = (mk_tapp head_ml prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___174_7839.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___174_7839.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7841; FStar_Extraction_ML_Syntax.loc = uu____7842})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___175_7848 = (mk_tapp head3 prefixAsMLTypes)
in {FStar_Extraction_ML_Syntax.expr = uu___175_7848.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___175_7848.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7849 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest))))))
end))
end
| uu____7858 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7652) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7910 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7910), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7911 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____7920 -> begin
(

let uu____7921 = (term_as_mlexpr g head2)
in (match (uu____7921) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____7939), f) -> begin
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

let uu____8006 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____8006) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____8037 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____8050 -> begin
(

let uu____8051 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____8051) with
| true -> begin
((lbs), (e'))
end
| uu____8062 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____8065 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____8065))
in (

let lb1 = (

let uu___176_8067 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___176_8067.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___176_8067.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___176_8067.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___176_8067.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____8037) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____8099 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____8099))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____8106 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____8110 = (FStar_Options.ml_ish ())
in (match (uu____8110) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____8113 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___177_8114 = lb
in {FStar_Syntax_Syntax.lbname = uu___177_8114.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___177_8114.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___177_8114.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___177_8114.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____8115 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____8137 -> (match (uu____8137) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____8157; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____8227 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____8227 (is_type_binder g))) -> begin
(

let uu____8240 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8240) with
| (bs1, c1) -> begin
(

let uu____8265 = (

let uu____8272 = (FStar_Util.prefix_until (fun x -> (

let uu____8308 = (is_type_binder g x)
in (not (uu____8308)))) bs1)
in (match (uu____8272) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____8396 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____8396)))
end))
in (match (uu____8265) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____8441 = (normalize_abs e)
in (FStar_All.pipe_right uu____8441 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____8483 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____8483) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____8536 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____8536) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____8624 uu____8625 -> (match (((uu____8624), (uu____8625))) with
| ((x, uu____8643), (y, uu____8645)) -> begin
(

let uu____8654 = (

let uu____8661 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____8661)))
in FStar_Syntax_Syntax.NT (uu____8654))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____8672 -> (match (uu____8672) with
| (a, uu____8678) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____8687 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____8705 -> (match (uu____8705) with
| (x, uu____8711) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8687), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____8719 = (is_fstar_value body1)
in (not (uu____8719)))
end
| uu____8720 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____8732 -> begin
rest_args
end)
in (

let polytype1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.push_unit polytype)
end
| uu____8734 -> begin
polytype
end)
in (

let body2 = (FStar_Syntax_Util.abs rest_args1 body1 copt)
in ((lbname_), (f_e), (((t2), (((targs), (polytype1))))), (add_unit), (body2))))))))))
end))
end
| uu____8770 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____8789) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8806 -> (match (uu____8806) with
| (a, uu____8812) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8821 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8833 -> (match (uu____8833) with
| (x, uu____8839) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8821), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8855 -> (match (uu____8855) with
| (bv, uu____8861) -> begin
(

let uu____8862 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8862 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8904) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8915 -> (match (uu____8915) with
| (a, uu____8921) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8930 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8942 -> (match (uu____8942) with
| (x, uu____8948) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8930), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8964 -> (match (uu____8964) with
| (bv, uu____8970) -> begin
(

let uu____8971 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____8971 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____9013) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9024 -> (match (uu____9024) with
| (a, uu____9030) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9039 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9051 -> (match (uu____9051) with
| (x, uu____9057) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9039), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9073 -> (match (uu____9073) with
| (bv, uu____9079) -> begin
(

let uu____9080 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9080 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____9122 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____9141 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____9245 -> (match (uu____9245) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____9380 -> (match (uu____9380) with
| (a, uu____9386) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (FStar_Pervasives_Native.snd polytype)
in (

let uu____9388 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____9388) with
| (e1, uu____9398) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____9465 = (FStar_List.fold_right (fun lb uu____9556 -> (match (uu____9556) with
| (env, lbs4) -> begin
(

let uu____9681 = lb
in (match (uu____9681) with
| (lbname, uu____9729, (t1, (uu____9731, polytype)), add_unit, uu____9734) -> begin
(

let uu____9747 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____9747) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____9465) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____9949 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____10024 = (term_as_mlexpr env_body e'1)
in (match (uu____10024) with
| (e'2, f', t') -> begin
(

let f = (

let uu____10041 = (

let uu____10044 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____10044)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____10041))
in (

let is_rec1 = (match ((Prims.op_Equality is_rec true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____10052 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____10053 = (

let uu____10054 = (

let uu____10055 = (

let uu____10056 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), ([]), (uu____10056)))
in (mk_MLE_Let top_level uu____10055 e'2))
in (

let uu____10067 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____10054 uu____10067)))
in ((uu____10053), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____10106 = (term_as_mlexpr g scrutinee)
in (match (uu____10106) with
| (e, f_e, t_e) -> begin
(

let uu____10122 = (check_pats_for_ite pats)
in (match (uu____10122) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____10179 = (term_as_mlexpr g then_e1)
in (match (uu____10179) with
| (then_mle, f_then, t_then) -> begin
(

let uu____10195 = (term_as_mlexpr g else_e1)
in (match (uu____10195) with
| (else_mle, f_else, t_else) -> begin
(

let uu____10211 = (

let uu____10220 = (type_leq g t_then t_else)
in (match (uu____10220) with
| true -> begin
((t_else), (no_lift))
end
| uu____10233 -> begin
(

let uu____10234 = (type_leq g t_else t_then)
in (match (uu____10234) with
| true -> begin
((t_then), (no_lift))
end
| uu____10247 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____10211) with
| (t_branch, maybe_lift1) -> begin
(

let uu____10268 = (

let uu____10269 = (

let uu____10270 = (

let uu____10279 = (maybe_lift1 then_mle t_then)
in (

let uu____10280 = (

let uu____10283 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____10283))
in ((e), (uu____10279), (uu____10280))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____10270))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____10269))
in (

let uu____10286 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____10268), (uu____10286), (t_branch))))
end))
end))
end))
end
| uu____10287 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____10302 -> begin
(

let uu____10303 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____10412 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____10412) with
| (pat, when_opt, branch1) -> begin
(

let uu____10456 = (extract_pat g pat t_e)
in (match (uu____10456) with
| (env, p, pat_t_compat) -> begin
(

let uu____10514 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____10536 = (term_as_mlexpr env w)
in (match (uu____10536) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end))
end)
in (match (uu____10514) with
| (when_opt1, f_when) -> begin
(

let uu____10585 = (term_as_mlexpr env branch1)
in (match (uu____10585) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____10619 = (FStar_All.pipe_right p (FStar_List.map (fun uu____10696 -> (match (uu____10696) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____10619)))
end))
end))
end))
end))) true))
in (match (uu____10303) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____10856 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____10861 -> (

let uu____10862 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____10863 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____10862 uu____10863)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____10888 = (

let uu____10897 = (

let uu____10914 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____10914))
in (FStar_All.pipe_left FStar_Util.right uu____10897))
in (match (uu____10888) with
| (uu____10957, fw, uu____10959, uu____10960) -> begin
(

let uu____10961 = (

let uu____10962 = (

let uu____10963 = (

let uu____10970 = (

let uu____10973 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____10973)::[])
in ((fw), (uu____10970)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____10963))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____10962))
in ((uu____10961), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____10976, uu____10977, (uu____10978, f_first, t_first)))::rest -> begin
(

let uu____11038 = (FStar_List.fold_left (fun uu____11080 uu____11081 -> (match (((uu____11080), (uu____11081))) with
| ((topt, f), (uu____11138, uu____11139, (uu____11140, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____11196 = (type_leq g t1 t_branch)
in (match (uu____11196) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____11199 -> begin
(

let uu____11200 = (type_leq g t_branch t1)
in (match (uu____11200) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____11203 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____11038) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____11295 -> (match (uu____11295) with
| (p, (wopt, uu____11324), (b1, uu____11326, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____11345) -> begin
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

let uu____11350 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____11350), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____11373 = (

let uu____11378 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11378))
in (match (uu____11373) with
| (uu____11403, fstar_disc_type) -> begin
(

let wildcards = (

let uu____11412 = (

let uu____11413 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____11413.FStar_Syntax_Syntax.n)
in (match (uu____11412) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11423) -> begin
(

let uu____11440 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___170_11472 -> (match (uu___170_11472) with
| (uu____11479, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11480))) -> begin
true
end
| uu____11483 -> begin
false
end))))
in (FStar_All.pipe_right uu____11440 (FStar_List.map (fun uu____11516 -> (

let uu____11523 = (fresh "_")
in ((uu____11523), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____11524 -> begin
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

let uu____11535 = (

let uu____11536 = (

let uu____11547 = (

let uu____11548 = (

let uu____11549 = (

let uu____11564 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), (mlid)))))
in (

let uu____11567 = (

let uu____11578 = (

let uu____11587 = (

let uu____11588 = (

let uu____11595 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____11595), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____11588))
in (

let uu____11598 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____11587), (FStar_Pervasives_Native.None), (uu____11598))))
in (

let uu____11601 = (

let uu____11612 = (

let uu____11621 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____11621)))
in (uu____11612)::[])
in (uu____11578)::uu____11601))
in ((uu____11564), (uu____11567))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____11549))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11548))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____11547)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____11536))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11535))
in (

let uu____11676 = (

let uu____11677 = (

let uu____11680 = (

let uu____11681 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____11681; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____11680)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____11677)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____11676)))))))
end)))




