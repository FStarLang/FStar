
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


let err_uninst : 'Auu____126 'Auu____127 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * 'Auu____127) Prims.list * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Syntax_Syntax.term  ->  'Auu____126 = (fun env t uu____152 app -> (match (uu____152) with
| (vars, ty) -> begin
(

let uu____178 = (

let uu____179 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____180 = (

let uu____181 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____181 (FStar_String.concat ", ")))
in (

let uu____198 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____199 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____179 uu____180 uu____198 uu____199)))))
in (fail t.FStar_Syntax_Syntax.pos uu____178))
end))


let err_ill_typed_application : 'Auu____212 'Auu____213 . FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * 'Auu____213) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  'Auu____212 = (fun env t args ty -> (

let uu____242 = (

let uu____243 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____244 = (

let uu____245 = (FStar_All.pipe_right args (FStar_List.map (fun uu____263 -> (match (uu____263) with
| (x, uu____269) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____245 (FStar_String.concat " ")))
in (

let uu____272 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" uu____243 uu____244 uu____272))))
in (fail t.FStar_Syntax_Syntax.pos uu____242)))


let err_value_restriction : 'Auu____277 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____277 = (fun t -> (

let uu____286 = (

let uu____287 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____288 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____287 uu____288)))
in (fail t.FStar_Syntax_Syntax.pos uu____286)))


let err_unexpected_eff : 'Auu____297 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  'Auu____297 = (fun t f0 f1 -> (

let uu____314 = (

let uu____315 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" uu____315 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos uu____314)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____332 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____332) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____337 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____337) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____348, c) -> begin
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
| uu____358 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____359 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____381 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____381) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____384 -> begin
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

let uu____400 = (

let uu____401 = (FStar_Syntax_Subst.compress t1)
in uu____401.FStar_Syntax_Syntax.n)
in (match (uu____400) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____404) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____429) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____456) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____463) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____480) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____481) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____482) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____483) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____484, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____502) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____504 = (

let uu____505 = (FStar_Syntax_Subst.compress t2)
in uu____505.FStar_Syntax_Syntax.n)
in (match (uu____504) with
| FStar_Syntax_Syntax.Tm_fvar (uu____508) -> begin
false
end
| uu____509 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____510) -> begin
(

let uu____525 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____525) with
| (head1, uu____541) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____563) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____569) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____574, body, uu____576) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____597, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____615, branches) -> begin
(match (branches) with
| ((uu____653, uu____654, e))::uu____656 -> begin
(is_arity env e)
end
| uu____703 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____729) -> begin
(

let uu____754 = (

let uu____755 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____755))
in (failwith uu____754))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____756 = (

let uu____757 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____757))
in (failwith uu____756))
end
| FStar_Syntax_Syntax.Tm_constant (uu____758) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____759) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____760) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____767) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Extraction_ML_UEnv.is_type_name env fv)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____782, t2) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____808; FStar_Syntax_Syntax.index = uu____809; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____813; FStar_Syntax_Syntax.index = uu____814; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____819, uu____820) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____862) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____869) -> begin
(

let uu____890 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____890) with
| (uu____895, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____912 = (

let uu____917 = (

let uu____918 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____918)::[])
in (FStar_Syntax_Subst.open_term uu____917 body))
in (match (uu____912) with
| (uu____919, body1) -> begin
(is_type_aux env body1)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____921, lbs), body) -> begin
(

let uu____938 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____938) with
| (uu____945, body1) -> begin
(is_type_aux env body1)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____951, branches) -> begin
(match (branches) with
| (b)::uu____990 -> begin
(

let uu____1035 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____1035) with
| (uu____1036, uu____1037, e) -> begin
(is_type_aux env e)
end))
end
| uu____1055 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1073) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1079) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> ((FStar_Extraction_ML_UEnv.debug env (fun uu____1112 -> (

let uu____1113 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1114 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "checking is_type (%s) %s\n" uu____1113 uu____1114)))));
(

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____1120 -> (match (b) with
| true -> begin
(

let uu____1121 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1122 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____1121 uu____1122)))
end
| uu____1123 -> begin
(

let uu____1124 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1125 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____1124 uu____1125)))
end)));
b;
));
))


let is_type_binder : 'Auu____1132 . FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____1132)  ->  Prims.bool = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1153 = (

let uu____1154 = (FStar_Syntax_Subst.compress t)
in uu____1154.FStar_Syntax_Syntax.n)
in (match (uu____1153) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1157; FStar_Syntax_Syntax.fv_delta = uu____1158; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____1159; FStar_Syntax_Syntax.fv_delta = uu____1160; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____1161))}) -> begin
true
end
| uu____1168 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1173 = (

let uu____1174 = (FStar_Syntax_Subst.compress t)
in uu____1174.FStar_Syntax_Syntax.n)
in (match (uu____1173) with
| FStar_Syntax_Syntax.Tm_constant (uu____1177) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____1178) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1179) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____1180) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1219 = (is_constructor head1)
in (match (uu____1219) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____1235 -> (match (uu____1235) with
| (te, uu____1241) -> begin
(is_fstar_value te)
end))))
end
| uu____1242 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1244) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1250, uu____1251) -> begin
(is_fstar_value t1)
end
| uu____1292 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____1297) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____1298) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____1299) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____1300) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____1311, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____1320, fields) -> begin
(FStar_Util.for_all (fun uu____1345 -> (match (uu____1345) with
| (uu____1350, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| uu____1352 -> begin
false
end))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(

let uu____1368 = (

let uu____1369 = (

let uu____1370 = (FStar_ST.read c)
in (FStar_Util.string_of_int uu____1370))
in (Prims.strcat x uu____1369))
in (

let uu____1373 = (FStar_ST.read c)
in ((uu____1368), (uu____1373))));
)))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1434 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1436 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1436) with
| true -> begin
(aux bs e' copt)
end
| uu____1437 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1442 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1442))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match (((FStar_List.length l) <> (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1520 -> begin
(

let uu____1521 = (FStar_List.hd l)
in (match (uu____1521) with
| (p1, w1, e1) -> begin
(

let uu____1555 = (

let uu____1564 = (FStar_List.tl l)
in (FStar_List.hd uu____1564))
in (match (uu____1555) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1638 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1704 = (erasable g f ty)
in (match (uu____1704) with
| true -> begin
(

let uu____1705 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1705) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1706 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1707 -> begin
e
end))
in ((e1), (f), (ty))))


let eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun t e -> (

let uu____1716 = (FStar_Extraction_ML_Util.doms_and_cod t)
in (match (uu____1716) with
| (ts, r) -> begin
(match ((ts = [])) with
| true -> begin
e
end
| uu____1731 -> begin
(

let vs = (FStar_List.map (fun uu____1744 -> (fresh "a")) ts)
in (

let vs_ts = (FStar_List.zip vs ts)
in (

let vs_es = (

let uu____1763 = (FStar_List.zip vs ts)
in (FStar_List.map (fun uu____1781 -> (match (uu____1781) with
| (v1, t1) -> begin
(FStar_Extraction_ML_Syntax.with_ty t1 (FStar_Extraction_ML_Syntax.MLE_Var (v1)))
end)) uu____1763))
in (

let body = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r) (FStar_Extraction_ML_Syntax.MLE_App (((e), (vs_es)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_Fun (((vs_ts), (body)))))))))
end)
end)))


let maybe_eta_expand : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun expect e -> (

let uu____1809 = ((FStar_Options.ml_no_eta_expand_coertions ()) || (

let uu____1811 = (FStar_Options.codegen ())
in (uu____1811 = FStar_Pervasives_Native.Some ("Kremlin"))))
in (match (uu____1809) with
| true -> begin
e
end
| uu____1816 -> begin
(eta_expand expect e)
end)))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1834 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____1834) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____1844 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1856 -> (

let uu____1857 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1858 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1859 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1857 uu____1858 uu____1859))))));
(

let uu____1860 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))))
in (maybe_eta_expand expect uu____1860));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1869 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1869) with
| FStar_Util.Inl (uu____1870, t) -> begin
t
end
| uu____1884 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1927) -> begin
(

let uu____1934 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1934) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____1938 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1941 = (is_top_ty mlt)
in (match (uu____1941) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1943 -> begin
mlt
end))))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____1947) -> begin
(

let uu____1948 = (

let uu____1949 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1949))
in (failwith uu____1948))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1950) -> begin
(

let uu____1975 = (

let uu____1976 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1976))
in (failwith uu____1975))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____1977 = (

let uu____1978 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1978))
in (failwith uu____1977))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1979) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1980) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1998) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____2003; FStar_Syntax_Syntax.index = uu____2004; FStar_Syntax_Syntax.sort = t2}, uu____2006) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2014) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2020, uu____2021) -> begin
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

let uu____2088 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2088) with
| (bs1, c1) -> begin
(

let uu____2095 = (binders_as_ml_binders env bs1)
in (match (uu____2095) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2122 = (

let uu____2129 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____2129))
in (match (uu____2122) with
| (ed, qualifiers) -> begin
(

let uu____2150 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____2150) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____2155 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____2157 = (FStar_List.fold_right (fun uu____2176 uu____2177 -> (match (((uu____2176), (uu____2177))) with
| ((uu____2198, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____2157) with
| (uu____2210, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____2235 = (

let uu____2236 = (FStar_Syntax_Util.un_uinst head1)
in uu____2236.FStar_Syntax_Syntax.n)
in (match (uu____2235) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____2263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____2263))
end
| uu____2280 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2283) -> begin
(

let uu____2304 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____2304) with
| (bs1, ty1) -> begin
(

let uu____2311 = (binders_as_ml_binders env bs1)
in (match (uu____2311) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____2336) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_let (uu____2337) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____2350) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____2374 -> (match (uu____2374) with
| (a, uu____2380) -> begin
(

let uu____2381 = (is_type g a)
in (match (uu____2381) with
| true -> begin
(term_as_mlty' g a)
end
| uu____2382 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____2386 = (

let uu____2399 = (FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____2399) with
| ((uu____2420, fvty), uu____2422) -> begin
(

let fvty1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) g.FStar_Extraction_ML_UEnv.tcenv fvty)
in (FStar_Syntax_Util.arrow_formals fvty1))
end))
in (match (uu____2386) with
| (formals, uu____2429) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____2473 = (FStar_Util.first_N n_args formals)
in (match (uu____2473) with
| (uu____2500, rest) -> begin
(

let uu____2526 = (FStar_List.map (fun uu____2534 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____2526))
end))
end
| uu____2539 -> begin
mlargs
end))
in (

let nm = (

let uu____2541 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____2541) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____2559 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2614 b -> (match (uu____2614) with
| (ml_bs, env) -> begin
(

let uu____2670 = (is_type_binder g b)
in (match (uu____2670) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____2696 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____2696), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____2723 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____2726 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____2726) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____2758 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____2758), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____2559) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____2868) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____2871, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____2875 -> begin
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
| uu____2905 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____2907 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____2908 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____2909 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____2912 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____2931 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____2931) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____2935 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____2962 -> begin
p
end)
end))
end
| uu____2965 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____3024 -> (

let uu____3025 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____3026 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____3025 uu____3026)))))
end
| uu____3027 -> begin
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

let uu____3066 = (

let uu____3067 = (

let uu____3074 = (

let uu____3077 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____3078 = (

let uu____3081 = (

let uu____3082 = (

let uu____3083 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_41 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_41)) uu____3083))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____3082))
in (uu____3081)::[])
in (uu____3077)::uu____3078))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____3074)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3067))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3066))
in (

let uu____3086 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____3086))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____3106 = (

let uu____3115 = (

let uu____3122 = (

let uu____3123 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____3123))
in ((uu____3122), ([])))
in FStar_Pervasives_Native.Some (uu____3115))
in (

let uu____3132 = (ok mlty)
in ((g), (uu____3106), (uu____3132))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3143 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3143) with
| (g1, x1) -> begin
(

let uu____3166 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3189 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3166)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____3200 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____3200) with
| (g1, x1) -> begin
(

let uu____3223 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3246 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____3223)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____3255) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____3294 = (

let uu____3299 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____3299) with
| FStar_Util.Inr (uu____3304, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____3306; FStar_Extraction_ML_Syntax.loc = uu____3307}, ttys, uu____3309) -> begin
((n1), (ttys))
end
| uu____3322 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____3294) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____3344 = (FStar_Util.first_N nTyVars pats)
in (match (uu____3344) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____3477 -> (match (uu____3477) with
| (p1, uu____3485) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____3490, t) -> begin
(term_as_mlty g t)
end
| uu____3496 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3500 -> (

let uu____3501 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____3501))));
(FStar_Pervasives.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____3503 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____3503))))
end)
with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end
in (

let uu____3532 = (FStar_Util.fold_map (fun g1 uu____3568 -> (match (uu____3568) with
| (p1, imp1) -> begin
(

let uu____3587 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None)
in (match (uu____3587) with
| (g2, p2, uu____3616) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____3532) with
| (g1, tyMLPats) -> begin
(

let uu____3677 = (FStar_Util.fold_map (fun uu____3741 uu____3742 -> (match (((uu____3741), (uu____3742))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____3835 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____3895 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____3835) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____3966 = (extract_one_pat false g2 p1 expected_ty)
in (match (uu____3966) with
| (g3, p2, uu____4007) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____3677) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____4125 = (

let uu____4136 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___139_4187 -> (match (uu___139_4187) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____4229 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4136 FStar_List.split))
in (match (uu____4125) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____4302 -> begin
false
end)
in (

let uu____4311 = (

let uu____4320 = (

let uu____4327 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____4330 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____4327), (uu____4330))))
in FStar_Pervasives_Native.Some (uu____4320))
in ((g2), (uu____4311), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____4421 = (extract_one_pat false g1 p1 expected_t1)
in (match (uu____4421) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____4478 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____4521 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____4521))
end))
in (

let uu____4522 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____4522) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____4664, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____4667 = (

let uu____4678 = (

let uu____4687 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____4687)))
in (uu____4678)::more_args)
in (eta_args uu____4667 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____4700, uu____4701) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____4724 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____4752, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____4784 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____4802 = (eta_args [] residualType)
in (match (uu____4802) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____4855 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____4855))
end
| uu____4856 -> begin
(

let uu____4867 = (FStar_List.unzip eargs)
in (match (uu____4867) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____4909 = (

let uu____4910 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____4910))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____4909))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____4919 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____4922, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4926; FStar_Extraction_ML_Syntax.loc = uu____4927}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____4954 -> begin
(

let uu____4957 = (

let uu____4964 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____4964), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4957))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4968; FStar_Extraction_ML_Syntax.loc = uu____4969}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____4977 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4977))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____4981; FStar_Extraction_ML_Syntax.loc = uu____4982}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____4984))) -> begin
(

let uu____4997 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____4997))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____5003 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5003))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____5007))) -> begin
(

let uu____5016 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5016))
end
| uu____5019 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____5038 = ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____5038) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____5039 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____5092 = (term_as_mlexpr' g t)
in (match (uu____5092) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5113 = (

let uu____5114 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5115 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____5116 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____5114 uu____5115 uu____5116 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____5113))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____5125 = (check_term_as_mlexpr' g t f ty)
in (match (uu____5125) with
| (e, t1) -> begin
(

let uu____5136 = (erase g e t1 f)
in (match (uu____5136) with
| (r, uu____5148, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____5158 = (term_as_mlexpr g e0)
in (match (uu____5158) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____5177 = (maybe_coerce g e t ty)
in ((uu____5177), (ty)))
end
| uu____5178 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____5195 = (

let uu____5196 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____5197 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____5198 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____5196 uu____5197 uu____5198))))
in (FStar_Util.print_string uu____5195))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5206 = (

let uu____5207 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5207))
in (failwith uu____5206))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5214) -> begin
(

let uu____5239 = (

let uu____5240 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5240))
in (failwith uu____5239))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5247) -> begin
(

let uu____5264 = (

let uu____5265 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5265))
in (failwith uu____5264))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5272) -> begin
(

let uu____5273 = (

let uu____5274 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5274))
in (failwith uu____5273))
end
| FStar_Syntax_Syntax.Tm_type (uu____5281) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5282) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5289) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____5307 = (term_as_mlexpr' g t1)
in (match (uu____5307) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____5353 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____5368)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____5398 = (

let uu____5405 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____5405))
in (match (uu____5398) with
| (ed, qualifiers) -> begin
(

let uu____5432 = (

let uu____5433 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____5433 Prims.op_Negation))
in (match (uu____5432) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____5442 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____5449 -> begin
(term_as_mlexpr' g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5451) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5457) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____5463 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____5463) with
| (uu____5476, ty, uu____5478) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____5480 = (

let uu____5481 = (

let uu____5482 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_42)) uu____5482))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5481))
in ((uu____5480), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____5483) -> begin
(

let uu____5484 = (is_type g t)
in (match (uu____5484) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5491 -> begin
(

let uu____5492 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5492) with
| (FStar_Util.Inl (uu____5505), uu____5506) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____5543, x, mltys, uu____5546), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____5592 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____5592), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____5593 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5600) -> begin
(

let uu____5601 = (is_type g t)
in (match (uu____5601) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____5608 -> begin
(

let uu____5609 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____5609) with
| (FStar_Util.Inl (uu____5622), uu____5623) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____5660, x, mltys, uu____5663), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____5709 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____5709), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____5710 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____5740 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____5740) with
| (bs1, body1) -> begin
(

let uu____5753 = (binders_as_ml_binders g bs1)
in (match (uu____5753) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____5786 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____5786) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____5787 -> begin
body1
end))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____5791 -> (

let uu____5792 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____5792))));
body1;
)
end)
in (

let uu____5793 = (term_as_mlexpr env body2)
in (match (uu____5793) with
| (ml_body, f, t1) -> begin
(

let uu____5809 = (FStar_List.fold_right (fun uu____5828 uu____5829 -> (match (((uu____5828), (uu____5829))) with
| ((uu____5850, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____5809) with
| (f1, tfun) -> begin
(

let uu____5870 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____5870), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____5877)); FStar_Syntax_Syntax.pos = uu____5878; FStar_Syntax_Syntax.vars = uu____5879}, uu____5880) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, (uu____5908)::((v1, uu____5910))::[]) when ((FStar_Syntax_Util.is_fstar_tactics_embed head1) && false) -> begin
(

let uu____5951 = (

let uu____5954 = (FStar_Syntax_Print.term_to_string v1)
in (FStar_Util.format2 "Trying to extract a quotation of %s" uu____5954))
in (

let s = (

let uu____5956 = (

let uu____5957 = (

let uu____5958 = (

let uu____5961 = (FStar_Util.marshal v1)
in (FStar_Util.bytes_of_string uu____5961))
in FStar_Extraction_ML_Syntax.MLC_Bytes (uu____5958))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____5957))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty uu____5956))
in (

let zero1 = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int ((("0"), (FStar_Pervasives_Native.None))))))
in (

let term_ty = (

let uu____5976 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.fstar_syntax_syntax_term FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (term_as_mlty g uu____5976))
in (

let marshal_from_string = (

let string_to_term_ty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_string_ty), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty)))
in (FStar_Extraction_ML_Syntax.with_ty string_to_term_ty (FStar_Extraction_ML_Syntax.MLE_Name (((("Marshal")::[]), ("from_string"))))))
in (

let uu____5981 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty) (FStar_Extraction_ML_Syntax.MLE_App (((marshal_from_string), ((s)::(zero1)::[])))))
in ((uu____5981), (FStar_Extraction_ML_Syntax.E_PURE), (term_ty))))))))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun rc -> ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.existsb (fun uu___140_6013 -> (match (uu___140_6013) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____6014 -> begin
false
end))))))
in (

let uu____6015 = (

let uu____6020 = (

let uu____6021 = (FStar_Syntax_Subst.compress head1)
in uu____6021.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____6020)))
in (match (uu____6015) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____6030), uu____6031) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6049, FStar_Syntax_Syntax.Tm_abs (bs, uu____6051, FStar_Pervasives_Native.Some (rc))) when (is_total rc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____6072, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____6074 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6074))
in (

let tm = (

let uu____6084 = (

let uu____6085 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____6086 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6085 uu____6086)))
in (uu____6084 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr' g tm)))
end
| uu____6095 -> begin
(

let rec extract_app = (fun is_data uu____6140 uu____6141 restArgs -> (match (((uu____6140), (uu____6141))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____6231) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____6253 -> begin
false
end))
in (

let uu____6254 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____6279 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (([]), (uu____6279)))
end
| uu____6310 -> begin
(FStar_List.fold_left (fun uu____6333 uu____6334 -> (match (((uu____6333), (uu____6334))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((f1 = FStar_Extraction_ML_Syntax.E_PURE) || (f1 = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____6435 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____6437 = (

let uu____6440 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____6440)::out_args)
in (((((x), (arg)))::lbs), (uu____6437))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____6254) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____6490 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____6490))
in (

let l_app = (FStar_List.fold_right (fun uu____6502 out -> (match (uu____6502) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____6523))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____6554 = (

let uu____6559 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____6559), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____6554 rest))
end
| (((e0, uu____6571))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____6603 = (term_as_mlexpr g e0)
in (match (uu____6603) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____6620 = (

let uu____6625 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____6625), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____6620 rest)))
end)))
end
| uu____6636 -> begin
(

let uu____6649 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____6649) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____6706 args1 -> (match (uu____6706) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____6738)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6816))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____6818, f', t3)) -> begin
(

let uu____6855 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____6855 t3))
end
| uu____6856 -> begin
((args2), (f1), (t2))
end))
in (

let uu____6881 = (remove_implicits args1 f t1)
in (match (uu____6881) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____6937 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____6950 = (is_type g t)
in (match (uu____6950) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____6957 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid) && (

let uu____6967 = (

let uu____6968 = (FStar_Extraction_ML_Syntax.string_of_mlpath g.FStar_Extraction_ML_UEnv.currentModule)
in (uu____6968 = "FStar.Tactics.Builtins"))
in (not (uu____6967)))) -> begin
(match (args) with
| (a)::(b)::[] -> begin
(term_as_mlexpr g (FStar_Pervasives_Native.fst a))
end
| uu____7009 -> begin
(

let uu____7018 = (FStar_Syntax_Print.args_to_string args)
in (failwith uu____7018))
end)
end
| FStar_Syntax_Syntax.Tm_name (uu____7025) -> begin
(

let uu____7026 = (

let uu____7039 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7039) with
| (FStar_Util.Inr (uu____7058, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7103 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7026) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7153))::uu____7154 -> begin
(is_type g a)
end
| uu____7173 -> begin
false
end)
in (

let uu____7182 = (match (vars) with
| (uu____7211)::uu____7212 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7223 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7251 = (FStar_Util.first_N n1 args)
in (match (uu____7251) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7340 -> (match (uu____7340) with
| (x, uu____7346) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7349) -> begin
(

let uu___144_7350 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___144_7350.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___144_7350.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7351) -> begin
(

let uu___144_7352 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___144_7352.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___144_7352.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7354; FStar_Extraction_ML_Syntax.loc = uu____7355})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___145_7361 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___145_7361.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___145_7361.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7362 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____7371 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7182) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7423 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7423), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7424 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7433) -> begin
(

let uu____7434 = (

let uu____7447 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____7447) with
| (FStar_Util.Inr (uu____7466, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____7511 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____7434) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____7561))::uu____7562 -> begin
(is_type g a)
end
| uu____7581 -> begin
false
end)
in (

let uu____7590 = (match (vars) with
| (uu____7619)::uu____7620 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____7631 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____7659 = (FStar_Util.first_N n1 args)
in (match (uu____7659) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____7748 -> (match (uu____7748) with
| (x, uu____7754) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____7757) -> begin
(

let uu___144_7758 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___144_7758.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___144_7758.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____7759) -> begin
(

let uu___144_7760 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___144_7760.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___144_7760.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____7762; FStar_Extraction_ML_Syntax.loc = uu____7763})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___145_7769 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___145_7769.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___145_7769.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____7770 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____7779 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____7590) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____7831 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____7831), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____7832 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____7841 -> begin
(

let uu____7842 = (term_as_mlexpr g head2)
in (match (uu____7842) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____7860), f) -> begin
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

let uu____7927 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____7927) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____7958 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____7971 -> begin
(

let uu____7972 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____7972) with
| true -> begin
((lbs), (e'))
end
| uu____7983 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____7986 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____7986))
in (

let lb1 = (

let uu___146_7988 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___146_7988.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_7988.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_7988.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___146_7988.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____7958) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____8020 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____8020))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____8027 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____8031 = (FStar_Options.ml_ish ())
in (match (uu____8031) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____8034 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___147_8035 = lb
in {FStar_Syntax_Syntax.lbname = uu___147_8035.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___147_8035.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___147_8035.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___147_8035.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____8036 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____8058 -> (match (uu____8058) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____8078; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____8148 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____8148 (is_type_binder g))) -> begin
(

let uu____8161 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8161) with
| (bs1, c1) -> begin
(

let uu____8186 = (

let uu____8193 = (FStar_Util.prefix_until (fun x -> (

let uu____8229 = (is_type_binder g x)
in (not (uu____8229)))) bs1)
in (match (uu____8193) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____8317 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____8317)))
end))
in (match (uu____8186) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____8362 = (normalize_abs e)
in (FStar_All.pipe_right uu____8362 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____8404 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____8404) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____8457 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____8457) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____8545 uu____8546 -> (match (((uu____8545), (uu____8546))) with
| ((x, uu____8564), (y, uu____8566)) -> begin
(

let uu____8575 = (

let uu____8582 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____8582)))
in FStar_Syntax_Syntax.NT (uu____8575))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____8593 -> (match (uu____8593) with
| (a, uu____8599) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____8612 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____8642 -> (match (uu____8642) with
| (x, uu____8652) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8612), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____8664 = (is_fstar_value body1)
in (not (uu____8664)))
end
| uu____8665 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____8677 -> begin
rest_args
end)
in (

let body2 = (match (rest_args1) with
| [] -> begin
body1
end
| uu____8679 -> begin
(FStar_Syntax_Util.abs rest_args1 body1 copt)
end)
in ((lbname_), (f_e), (((t2), (((targs), (polytype))))), (add_unit), (body2)))))))))
end))
end
| uu____8746 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____8765) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8782 -> (match (uu____8782) with
| (a, uu____8788) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8801 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8825 -> (match (uu____8825) with
| (x, uu____8835) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8801), (expected_t)))
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
| FStar_Syntax_Syntax.Tm_fvar (uu____8916) -> begin
(

let env = (FStar_List.fold_left (fun env uu____8927 -> (match (uu____8927) with
| (a, uu____8933) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____8946 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____8970 -> (match (uu____8970) with
| (x, uu____8980) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____8946), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9000 -> (match (uu____9000) with
| (bv, uu____9006) -> begin
(

let uu____9007 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9007 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____9061) -> begin
(

let env = (FStar_List.fold_left (fun env uu____9072 -> (match (uu____9072) with
| (a, uu____9078) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____9091 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9115 -> (match (uu____9115) with
| (x, uu____9125) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____9091), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____9145 -> (match (uu____9145) with
| (bv, uu____9151) -> begin
(

let uu____9152 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____9152 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____9206 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____9225 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____9329 -> (match (uu____9329) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____9464 -> (match (uu____9464) with
| (a, uu____9470) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((FStar_Pervasives_Native.snd polytype))))
end
| uu____9472 -> begin
(FStar_Pervasives_Native.snd polytype)
end)
in (

let polytype1 = (((FStar_Pervasives_Native.fst polytype)), (expected_t))
in (

let uu____9478 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____9478) with
| (e1, uu____9488) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype1); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end)))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____9555 = (FStar_List.fold_right (fun lb uu____9646 -> (match (uu____9646) with
| (env, lbs4) -> begin
(

let uu____9771 = lb
in (match (uu____9771) with
| (lbname, uu____9819, (t1, (uu____9821, polytype)), add_unit, uu____9824) -> begin
(

let uu____9837 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____9837) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____9555) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____10039 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____10114 = (term_as_mlexpr env_body e'1)
in (match (uu____10114) with
| (e'2, f', t') -> begin
(

let f = (

let uu____10131 = (

let uu____10134 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____10134)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____10131))
in (

let is_rec1 = (match ((is_rec = true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____10142 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____10143 = (

let uu____10144 = (

let uu____10145 = (

let uu____10146 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), ([]), (uu____10146)))
in (mk_MLE_Let top_level uu____10145 e'2))
in (

let uu____10157 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____10144 uu____10157)))
in ((uu____10143), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____10196 = (term_as_mlexpr g scrutinee)
in (match (uu____10196) with
| (e, f_e, t_e) -> begin
(

let uu____10212 = (check_pats_for_ite pats)
in (match (uu____10212) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____10269 = (term_as_mlexpr g then_e1)
in (match (uu____10269) with
| (then_mle, f_then, t_then) -> begin
(

let uu____10285 = (term_as_mlexpr g else_e1)
in (match (uu____10285) with
| (else_mle, f_else, t_else) -> begin
(

let uu____10301 = (

let uu____10310 = (type_leq g t_then t_else)
in (match (uu____10310) with
| true -> begin
((t_else), (no_lift))
end
| uu____10323 -> begin
(

let uu____10324 = (type_leq g t_else t_then)
in (match (uu____10324) with
| true -> begin
((t_then), (no_lift))
end
| uu____10337 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____10301) with
| (t_branch, maybe_lift1) -> begin
(

let uu____10358 = (

let uu____10359 = (

let uu____10360 = (

let uu____10369 = (maybe_lift1 then_mle t_then)
in (

let uu____10370 = (

let uu____10373 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____10373))
in ((e), (uu____10369), (uu____10370))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____10360))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____10359))
in (

let uu____10376 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____10358), (uu____10376), (t_branch))))
end))
end))
end))
end
| uu____10377 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____10392 -> begin
(

let uu____10393 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____10502 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____10502) with
| (pat, when_opt, branch1) -> begin
(

let uu____10546 = (extract_pat g pat t_e)
in (match (uu____10546) with
| (env, p, pat_t_compat) -> begin
(

let uu____10604 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____10626 = (term_as_mlexpr env w)
in (match (uu____10626) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end))
end)
in (match (uu____10604) with
| (when_opt1, f_when) -> begin
(

let uu____10675 = (term_as_mlexpr env branch1)
in (match (uu____10675) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____10709 = (FStar_All.pipe_right p (FStar_List.map (fun uu____10786 -> (match (uu____10786) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____10709)))
end))
end))
end))
end))) true))
in (match (uu____10393) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____10946 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____10951 -> (

let uu____10952 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____10953 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____10952 uu____10953)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____10978 = (

let uu____10987 = (

let uu____11004 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____11004))
in (FStar_All.pipe_left FStar_Util.right uu____10987))
in (match (uu____10978) with
| (uu____11047, fw, uu____11049, uu____11050) -> begin
(

let uu____11051 = (

let uu____11052 = (

let uu____11053 = (

let uu____11060 = (

let uu____11063 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____11063)::[])
in ((fw), (uu____11060)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____11053))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____11052))
in ((uu____11051), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____11066, uu____11067, (uu____11068, f_first, t_first)))::rest -> begin
(

let uu____11128 = (FStar_List.fold_left (fun uu____11170 uu____11171 -> (match (((uu____11170), (uu____11171))) with
| ((topt, f), (uu____11228, uu____11229, (uu____11230, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____11286 = (type_leq g t1 t_branch)
in (match (uu____11286) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____11289 -> begin
(

let uu____11290 = (type_leq g t_branch t1)
in (match (uu____11290) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____11293 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____11128) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____11385 -> (match (uu____11385) with
| (p, (wopt, uu____11414), (b1, uu____11416, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____11435) -> begin
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

let uu____11440 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____11440), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____11463 = (

let uu____11468 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11468))
in (match (uu____11463) with
| (uu____11493, fstar_disc_type) -> begin
(

let wildcards = (

let uu____11506 = (

let uu____11507 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____11507.FStar_Syntax_Syntax.n)
in (match (uu____11506) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____11521) -> begin
(

let uu____11538 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___141_11570 -> (match (uu___141_11570) with
| (uu____11577, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11578))) -> begin
true
end
| uu____11581 -> begin
false
end))))
in (FStar_All.pipe_right uu____11538 (FStar_List.map (fun uu____11622 -> (

let uu____11629 = (fresh "_")
in ((uu____11629), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____11638 -> begin
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

let uu____11657 = (

let uu____11658 = (

let uu____11669 = (

let uu____11670 = (

let uu____11671 = (

let uu____11686 = (

let uu____11687 = (

let uu____11688 = (

let uu____11689 = (FStar_Extraction_ML_Syntax.idsym mlid)
in (([]), (uu____11689)))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____11688))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) uu____11687))
in (

let uu____11692 = (

let uu____11703 = (

let uu____11712 = (

let uu____11713 = (

let uu____11720 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____11720), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____11713))
in (

let uu____11723 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____11712), (FStar_Pervasives_Native.None), (uu____11723))))
in (

let uu____11726 = (

let uu____11737 = (

let uu____11746 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____11746)))
in (uu____11737)::[])
in (uu____11703)::uu____11726))
in ((uu____11686), (uu____11692))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____11671))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11670))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____11669)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____11658))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11657))
in (

let uu____11821 = (

let uu____11822 = (

let uu____11825 = (

let uu____11826 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____11826; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____11825)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____11822)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____11821)))))))
end)))




