
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

let uu____125 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.fst))
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
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (

let uu____238 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____238) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (uu____244, c) -> begin
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
| uu____252 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____253 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____266 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____266) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____268 -> begin
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

let uu____279 = (

let uu____280 = (FStar_Syntax_Subst.compress t1)
in uu____280.FStar_Syntax_Syntax.n)
in (match (uu____279) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____283) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____304) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_meta (uu____322) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uvar (uu____327) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____336) -> begin
false
end
| FStar_Syntax_Syntax.Tm_name (uu____337) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____338) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____339) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____340, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____352) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____354 = (

let uu____355 = (FStar_Syntax_Subst.compress t2)
in uu____355.FStar_Syntax_Syntax.n)
in (match (uu____354) with
| FStar_Syntax_Syntax.Tm_fvar (uu____358) -> begin
false
end
| uu____359 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____360) -> begin
(

let uu____370 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____370) with
| (head1, uu____381) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____397) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____403) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_abs (uu____408, body, uu____410) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____433, body) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____445, branches) -> begin
(match (branches) with
| ((uu____473, uu____474, e))::uu____476 -> begin
(is_arity env e)
end
| uu____512 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____531) -> begin
(

let uu____552 = (

let uu____553 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____553))
in (failwith uu____552))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____554 = (

let uu____555 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____555))
in (failwith uu____554))
end
| FStar_Syntax_Syntax.Tm_constant (uu____556) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____557) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____558) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____563) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____573 = (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____573) with
| true -> begin
true
end
| uu____578 -> begin
(

let uu____579 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____579) with
| ((uu____588, t2), uu____590) -> begin
(is_arity env t2)
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____593, t2) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = uu____607; FStar_Syntax_Syntax.index = uu____608; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = uu____612; FStar_Syntax_Syntax.index = uu____613; FStar_Syntax_Syntax.sort = t2}) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____618, uu____619) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____649) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____654, body, uu____656) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____679, body) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____691, branches) -> begin
(match (branches) with
| ((uu____719, uu____720, e))::uu____722 -> begin
(is_type_aux env e)
end
| uu____758 -> begin
false
end)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____771) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____777) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____800 -> (match (b) with
| true -> begin
(

let uu____801 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____802 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____801 uu____802)))
end
| uu____803 -> begin
(

let uu____804 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____805 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____804 uu____805)))
end)));
b;
)))


let is_type_binder = (fun env x -> (is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____825 = (

let uu____826 = (FStar_Syntax_Subst.compress t)
in uu____826.FStar_Syntax_Syntax.n)
in (match (uu____825) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____829; FStar_Syntax_Syntax.fv_delta = uu____830; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____834; FStar_Syntax_Syntax.fv_delta = uu____835; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____836))}) -> begin
true
end
| uu____843 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____847 = (

let uu____848 = (FStar_Syntax_Subst.compress t)
in uu____848.FStar_Syntax_Syntax.n)
in (match (uu____847) with
| FStar_Syntax_Syntax.Tm_constant (uu____851) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____852) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (uu____853) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____854) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____885 = (is_constructor head1)
in (match (uu____885) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____893 -> (match (uu____893) with
| (te, uu____897) -> begin
(is_fstar_value te)
end))))
end
| uu____898 -> begin
false
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____900) -> begin
(is_fstar_value t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____906, uu____907) -> begin
(is_fstar_value t1)
end
| uu____936 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Const (uu____940) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____941) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Name (uu____942) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_Fun (uu____943) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLE_CTor (uu____949, exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (exps) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____955, fields) -> begin
(FStar_Util.for_all (fun uu____967 -> (match (uu____967) with
| (uu____970, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| uu____972 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____1032 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____1034 = (FStar_Syntax_Util.is_fun e')
in (match (uu____1034) with
| true -> begin
(aux bs e' copt)
end
| uu____1035 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 FStar_Pervasives_Native.None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____1043 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1043))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun l -> (

let def = ((false), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
in (match (((FStar_List.length l) <> (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____1086 -> begin
(

let uu____1087 = (FStar_List.hd l)
in (match (uu____1087) with
| (p1, w1, e1) -> begin
(

let uu____1106 = (

let uu____1111 = (FStar_List.tl l)
in (FStar_List.hd uu____1111))
in (match (uu____1106) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (FStar_Pervasives_Native.Some (e1)), (FStar_Pervasives_Native.Some (e2)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (FStar_Pervasives_Native.Some (e2)), (FStar_Pervasives_Native.Some (e1)))
end
| uu____1150 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1193 = (erasable g f ty)
in (match (uu____1193) with
| true -> begin
(

let uu____1194 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1194) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1195 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1196 -> begin
e
end))
in ((e1), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1210 = (type_leq_c g (FStar_Pervasives_Native.Some (e)) ty1 expect)
in (match (uu____1210) with
| (true, FStar_Pervasives_Native.Some (e')) -> begin
e'
end
| uu____1216 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1221 -> (

let uu____1222 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1223 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1224 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1222 uu____1223 uu____1224))))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1231 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1231) with
| FStar_Util.Inl (uu____1232, t) -> begin
t
end
| uu____1240 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1276) -> begin
(

let uu____1280 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1280) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (t1) -> begin
(is_top_ty t1)
end))
end
| uu____1283 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1286 = (is_top_ty mlt)
in (match (uu____1286) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1288 -> begin
mlt
end))))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____1292) -> begin
(

let uu____1293 = (

let uu____1294 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1294))
in (failwith uu____1293))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1295) -> begin
(

let uu____1316 = (

let uu____1317 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1317))
in (failwith uu____1316))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____1318 = (

let uu____1319 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1319))
in (failwith uu____1318))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1320) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1321) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1331) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____1336; FStar_Syntax_Syntax.index = uu____1337; FStar_Syntax_Syntax.sort = t2}, uu____1339) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1347) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1353, uu____1354) -> begin
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

let uu____1401 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1401) with
| (bs1, c1) -> begin
(

let uu____1406 = (binders_as_ml_binders env bs1)
in (match (uu____1406) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____1422 = (

let uu____1426 = (FStar_TypeChecker_Env.effect_decl_opt env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (FStar_Util.must uu____1426))
in (match (uu____1422) with
| (ed, qualifiers) -> begin
(

let uu____1438 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____1438) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____1442 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))
end)))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____1444 = (FStar_List.fold_right (fun uu____1451 uu____1452 -> (match (((uu____1451), (uu____1452))) with
| ((uu____1463, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____1444) with
| (uu____1471, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____1490 = (

let uu____1491 = (FStar_Syntax_Util.un_uinst head1)
in uu____1491.FStar_Syntax_Syntax.n)
in (match (uu____1490) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____1512 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____1512))
end
| uu____1528 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____1531) -> begin
(

let uu____1554 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____1554) with
| (bs1, ty1) -> begin
(

let uu____1559 = (binders_as_ml_binders env bs1)
in (match (uu____1559) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____1573) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_let (uu____1574) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_match (uu____1582) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____1599 -> (match (uu____1599) with
| (a, uu____1603) -> begin
(

let uu____1604 = (is_type g a)
in (match (uu____1604) with
| true -> begin
(term_as_mlty' g a)
end
| uu____1605 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____1609 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (uu____1609) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____1653 = (FStar_Util.first_N n_args formals)
in (match (uu____1653) with
| (uu____1667, rest) -> begin
(

let uu____1681 = (FStar_List.map (fun uu____1685 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____1681))
end))
end
| uu____1688 -> begin
mlargs
end))
in (

let nm = (

let uu____1690 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____1690) with
| FStar_Pervasives_Native.Some (p) -> begin
p
end
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____1705 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1729 b -> (match (uu____1729) with
| (ml_bs, env) -> begin
(

let uu____1759 = (is_type_binder g b)
in (match (uu____1759) with
| true -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____1774 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____1774), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____1788 -> begin
(

let b1 = (FStar_Pervasives_Native.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____1791 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____1791) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____1809 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____1809), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____1705) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____1869) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____1871, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____1874 -> begin
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
| uu____1894 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1896 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____1897 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____1898 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____1900 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(

let uu____1913 = (FStar_Extraction_ML_Util.is_xtuple d)
in (match (uu____1913) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____1916 -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____1932 -> begin
p
end)
end))
end
| uu____1934 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____1970 -> (

let uu____1971 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____1972 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____1971 uu____1972)))))
end
| uu____1973 -> begin
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

let uu____1995 = (

let uu____1996 = (

let uu____2000 = (

let uu____2002 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____2003 = (

let uu____2005 = (

let uu____2006 = (

let uu____2007 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_31)) uu____2007))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____2006))
in (uu____2005)::[])
in (uu____2002)::uu____2003))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____2000)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1996))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1995))
in (

let uu____2009 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____2009))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____2021 = (

let uu____2026 = (

let uu____2030 = (

let uu____2031 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____2031))
in ((uu____2030), ([])))
in FStar_Pervasives_Native.Some (uu____2026))
in (

let uu____2036 = (ok mlty)
in ((g), (uu____2021), (uu____2036))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____2043 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____2043) with
| (g1, x1) -> begin
(

let uu____2056 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2068 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____2056)))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____2075 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____2075) with
| (g1, x1) -> begin
(

let uu____2088 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2100 -> begin
FStar_Pervasives_Native.Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____2088)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____2105) -> begin
((g), (FStar_Pervasives_Native.None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____2129 = (

let uu____2132 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____2132) with
| FStar_Util.Inr (uu____2135, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____2137; FStar_Extraction_ML_Syntax.loc = uu____2138}, ttys, uu____2140) -> begin
((n1), (ttys))
end
| uu____2147 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____2129) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (FStar_Pervasives_Native.fst tys))
in (

let uu____2161 = (FStar_Util.first_N nTyVars pats)
in (match (uu____2161) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____2235 -> (match (uu____2235) with
| (p1, uu____2241) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2246, t) -> begin
(term_as_mlty g t)
end
| uu____2252 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2254 -> (

let uu____2255 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____2255))));
(FStar_Pervasives.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____2257 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in FStar_Pervasives_Native.Some (uu____2257))))
end)
with
| Un_extractable -> begin
FStar_Pervasives_Native.None
end
in (

let uu____2272 = (FStar_Util.fold_map (fun g1 uu____2287 -> (match (uu____2287) with
| (p1, imp1) -> begin
(

let uu____2298 = (extract_one_pat true g1 p1 FStar_Pervasives_Native.None)
in (match (uu____2298) with
| (g2, p2, uu____2314) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____2272) with
| (g1, tyMLPats) -> begin
(

let uu____2346 = (FStar_Util.fold_map (fun uu____2372 uu____2373 -> (match (((uu____2372), (uu____2373))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____2422 = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ((hd1)::rest, res) -> begin
((FStar_Pervasives_Native.Some (((rest), (res)))), (FStar_Pervasives_Native.Some (hd1)))
end
| uu____2454 -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____2422) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____2491 = (extract_one_pat false g2 p1 expected_ty)
in (match (uu____2491) with
| (g3, p2, uu____2513) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____2346) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____2574 = (

let uu____2580 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___137_2605 -> (match (uu___137_2605) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| uu____2627 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2580 FStar_List.split))
in (match (uu____2574) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| FStar_Pervasives_Native.Some ([], t) -> begin
(ok t)
end
| uu____2666 -> begin
false
end)
in (

let uu____2671 = (

let uu____2676 = (

let uu____2680 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____2682 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____2680), (uu____2682))))
in FStar_Pervasives_Native.Some (uu____2676))
in ((g2), (uu____2671), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun g1 p1 expected_t1 -> (

let uu____2736 = (extract_one_pat false g1 p1 expected_t1)
in (match (uu____2736) with
| (g2, FStar_Pervasives_Native.Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____2767 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hd1)::tl1 -> begin
(

let uu____2792 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in FStar_Pervasives_Native.Some (uu____2792))
end))
in (

let uu____2793 = (extract_one_pat1 g p (FStar_Pervasives_Native.Some (expected_t)))
in (match (uu____2793) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2875, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____2878 = (

let uu____2884 = (

let uu____2889 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____2889)))
in (uu____2884)::more_args)
in (eta_args uu____2878 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____2896, uu____2897) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____2909 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2927, args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____2946 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____2959 = (eta_args [] residualType)
in (match (uu____2959) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____2987 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____2987))
end
| uu____2988 -> begin
(

let uu____2994 = (FStar_List.unzip eargs)
in (match (uu____2994) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____3018 = (

let uu____3019 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____3019))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____3018))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____3024 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____3026, FStar_Pervasives_Native.None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3029; FStar_Extraction_ML_Syntax.loc = uu____3030}, (mle)::args), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____3048 -> begin
(

let uu____3050 = (

let uu____3054 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____3054), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3050))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3057; FStar_Extraction_ML_Syntax.loc = uu____3058}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____3063 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3063))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3066; FStar_Extraction_ML_Syntax.loc = uu____3067}, mlargs), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____3069))) -> begin
(

let uu____3076 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3076))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) -> begin
(

let uu____3080 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3080))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (mlp), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____3083))) -> begin
(

let uu____3088 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3088))
end
| uu____3090 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____3103 = ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____3103) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____3104 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____3144 = (term_as_mlexpr' g t)
in (match (uu____3144) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3157 = (

let uu____3158 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3159 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____3160 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____3158 uu____3159 uu____3160 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____3157))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____3167 = (check_term_as_mlexpr' g t f ty)
in (match (uu____3167) with
| (e, t1) -> begin
(

let uu____3174 = (erase g e t1 f)
in (match (uu____3174) with
| (r, uu____3181, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____3189 = (term_as_mlexpr g e0)
in (match (uu____3189) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____3201 = (maybe_coerce g e t ty)
in ((uu____3201), (ty)))
end
| uu____3202 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3212 = (

let uu____3213 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3214 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____3215 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____3213 uu____3214 uu____3215))))
in (FStar_Util.print_string uu____3212))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3220 = (

let uu____3221 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3221))
in (failwith uu____3220))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3225) -> begin
(

let uu____3246 = (

let uu____3247 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3247))
in (failwith uu____3246))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3251) -> begin
(

let uu____3260 = (

let uu____3261 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3261))
in (failwith uu____3260))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3265) -> begin
(

let uu____3266 = (

let uu____3267 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3267))
in (failwith uu____3266))
end
| FStar_Syntax_Syntax.Tm_type (uu____3271) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_refine (uu____3272) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3277) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____3290 = (term_as_mlexpr' g t1)
in (match (uu____3290) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____3317 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____3326)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let uu____3349 = (

let uu____3353 = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv m)
in (FStar_Util.must uu____3353))
in (match (uu____3349) with
| (ed, qualifiers) -> begin
(

let uu____3368 = (

let uu____3369 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____3369 Prims.op_Negation))
in (match (uu____3368) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____3374 -> begin
(failwith "This should not happen (should have been handled at Tm_abs level)")
end))
end))
end
| uu____3378 -> begin
(term_as_mlexpr' g t2)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____3380) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3386) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3392 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____3392) with
| (uu____3399, ty, uu____3401) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____3403 = (

let uu____3404 = (

let uu____3405 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_32 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_32)) uu____3405))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3404))
in ((uu____3403), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| FStar_Syntax_Syntax.Tm_name (uu____3406) -> begin
(

let uu____3407 = (is_type g t)
in (match (uu____3407) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3411 -> begin
(

let uu____3412 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3412) with
| (FStar_Util.Inl (uu____3419), uu____3420) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____3439, x, mltys, uu____3442), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____3467 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____3467), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____3468 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3472) -> begin
(

let uu____3473 = (is_type g t)
in (match (uu____3473) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3477 -> begin
(

let uu____3478 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3478) with
| (FStar_Util.Inl (uu____3485), uu____3486) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____3505, x, mltys, uu____3508), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____3533 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____3533), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____3534 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____3563 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3563) with
| (bs1, body1) -> begin
(

let uu____3571 = (binders_as_ml_binders g bs1)
in (match (uu____3571) with
| (ml_bs, env) -> begin
(

let body2 = (match (copt) with
| FStar_Pervasives_Native.Some (c) -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3601 -> (match (c) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3606 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Computation lc: %s\n" uu____3606))
end
| FStar_Util.Inr (rc) -> begin
(FStar_Util.print1 "Computation rc: %s\n" (FStar_Ident.text_of_lid (FStar_Pervasives_Native.fst rc)))
end)));
(

let uu____3615 = (FStar_TypeChecker_Env.is_reifiable env.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____3615) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____3616 -> begin
body1
end));
)
end
| FStar_Pervasives_Native.None -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____3623 -> (

let uu____3624 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print1 "No computation type for: %s\n" uu____3624))));
body1;
)
end)
in (

let uu____3625 = (term_as_mlexpr env body2)
in (match (uu____3625) with
| (ml_body, f, t1) -> begin
(

let uu____3635 = (FStar_List.fold_right (fun uu____3642 uu____3643 -> (match (((uu____3642), (uu____3643))) with
| ((uu____3654, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____3635) with
| (f1, tfun) -> begin
(

let uu____3667 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____3667), (f1), (tfun)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3671)); FStar_Syntax_Syntax.tk = uu____3672; FStar_Syntax_Syntax.pos = uu____3673; FStar_Syntax_Syntax.vars = uu____3674}, uu____3675) -> begin
(failwith "Unreachable? Tm_app Const_reflect")
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun uu___139_3717 -> (match (uu___139_3717) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l, flags) -> begin
((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right flags (FStar_List.existsb (fun uu___138_3735 -> (match (uu___138_3735) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3736 -> begin
false
end)))))
end))
in (

let uu____3737 = (

let uu____3740 = (

let uu____3741 = (FStar_Syntax_Subst.compress head1)
in uu____3741.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____3740)))
in (match (uu____3737) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____3747), uu____3748) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____3758, FStar_Syntax_Syntax.Tm_abs (bs, uu____3760, FStar_Pervasives_Native.Some (lc))) when (is_total lc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____3789, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) -> begin
(

let e = (

let uu____3791 = (FStar_List.hd args)
in (FStar_TypeChecker_Util.reify_body_with_arg g.FStar_Extraction_ML_UEnv.tcenv head1 uu____3791))
in (

let tm = (

let uu____3799 = (

let uu____3800 = (FStar_TypeChecker_Util.remove_reify e)
in (

let uu____3801 = (FStar_List.tl args)
in (FStar_Syntax_Syntax.mk_Tm_app uu____3800 uu____3801)))
in (uu____3799 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (term_as_mlexpr' g tm)))
end
| uu____3810 -> begin
(

let rec extract_app = (fun is_data uu____3838 uu____3839 restArgs -> (match (((uu____3838), (uu____3839))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____3887) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____3901 -> begin
false
end))
in (

let uu____3902 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____3915 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map FStar_Pervasives_Native.fst))
in (([]), (uu____3915)))
end
| uu____3931 -> begin
(FStar_List.fold_left (fun uu____3940 uu____3941 -> (match (((uu____3940), (uu____3941))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((f1 = FStar_Extraction_ML_Syntax.E_PURE) || (f1 = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____3994 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____3996 = (

let uu____3998 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____3998)::out_args)
in (((((x), (arg)))::lbs), (uu____3996))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____3902) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____4025 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____4025))
in (

let l_app = (FStar_List.fold_right (fun uu____4030 out -> (match (uu____4030) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____4043))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____4061 = (

let uu____4064 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____4064), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____4061 rest))
end
| (((e0, uu____4071))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____4090 = (term_as_mlexpr g e0)
in (match (uu____4090) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____4101 = (

let uu____4104 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____4104), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____4101 rest)))
end)))
end
| uu____4110 -> begin
(

let uu____4117 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____4117) with
| FStar_Pervasives_Native.Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| FStar_Pervasives_Native.None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____4153 args1 -> (match (uu____4153) with
| (f, t1) -> begin
(match (is_data) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (uu____4172)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4222))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4224, f', t3)) -> begin
(

let uu____4249 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____4249 t3))
end
| uu____4250 -> begin
((args2), (f1), (t2))
end))
in (

let uu____4265 = (remove_implicits args1 f t1)
in (match (uu____4265) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____4298 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____4305 = (is_type g t)
in (match (uu____4305) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____4309 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (uu____4314) -> begin
(

let uu____4315 = (

let uu____4322 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____4322) with
| (FStar_Util.Inr (uu____4332, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____4357 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4315) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4386))::uu____4387 -> begin
(is_type g a)
end
| uu____4401 -> begin
false
end)
in (

let uu____4407 = (match (vars) with
| (uu____4424)::uu____4425 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____4432 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____4452 = (FStar_Util.first_N n1 args)
in (match (uu____4452) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4505 -> (match (uu____4505) with
| (x, uu____4509) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____4512) -> begin
(

let uu___143_4513 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4513.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4513.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____4514) -> begin
(

let uu___143_4515 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4515.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4515.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4517; FStar_Extraction_ML_Syntax.loc = uu____4518})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___144_4521 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___144_4521.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___144_4521.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____4522 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____4528 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____4407) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____4560 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____4560), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____4561 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4567) -> begin
(

let uu____4568 = (

let uu____4575 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____4575) with
| (FStar_Util.Inr (uu____4585, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____4610 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4568) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4639))::uu____4640 -> begin
(is_type g a)
end
| uu____4654 -> begin
false
end)
in (

let uu____4660 = (match (vars) with
| (uu____4677)::uu____4678 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____4685 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____4705 = (FStar_Util.first_N n1 args)
in (match (uu____4705) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4758 -> (match (uu____4758) with
| (x, uu____4762) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Name (uu____4765) -> begin
(

let uu___143_4766 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4766.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4766.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_Var (uu____4767) -> begin
(

let uu___143_4768 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4768.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4768.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4770; FStar_Extraction_ML_Syntax.loc = uu____4771})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___144_4774 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___144_4774.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___144_4774.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____4775 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____4781 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____4660) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____4813 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____4813), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____4814 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____4820 -> begin
(

let uu____4821 = (term_as_mlexpr g head2)
in (match (uu____4821) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector FStar_Pervasives_Native.None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____4833), f) -> begin
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

let uu____4887 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____4887) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____4908 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____4915 -> begin
(

let uu____4916 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4916) with
| true -> begin
((lbs), (e'))
end
| uu____4923 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____4926 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____4926))
in (

let lb1 = (

let uu___145_4928 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___145_4928.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___145_4928.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___145_4928.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___145_4928.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____4908) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____4945 = (FStar_Ident.lid_of_path (FStar_List.append (FStar_Pervasives_Native.fst g.FStar_Extraction_ML_UEnv.currentModule) (((FStar_Pervasives_Native.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____4945))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____4949 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____4953 = (FStar_Options.ml_ish ())
in (match (uu____4953) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____4956 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___146_4957 = lb
in {FStar_Syntax_Syntax.lbname = uu___146_4957.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_4957.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_4957.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_4957.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____4958 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____4971 -> (match (uu____4971) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____4982; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____5025 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____5025 (is_type_binder g))) -> begin
(

let uu____5032 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____5032) with
| (bs1, c1) -> begin
(

let uu____5046 = (

let uu____5051 = (FStar_Util.prefix_until (fun x -> (

let uu____5069 = (is_type_binder g x)
in (not (uu____5069)))) bs1)
in (match (uu____5051) with
| FStar_Pervasives_Native.None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| FStar_Pervasives_Native.Some (bs2, b, rest) -> begin
(

let uu____5117 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____5117)))
end))
in (match (uu____5046) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____5147 = (normalize_abs e)
in (FStar_All.pipe_right uu____5147 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, copt) -> begin
(

let uu____5182 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____5182) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____5212 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____5212) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____5255 uu____5256 -> (match (((uu____5255), (uu____5256))) with
| ((x, uu____5266), (y, uu____5268)) -> begin
(

let uu____5273 = (

let uu____5278 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____5278)))
in FStar_Syntax_Syntax.NT (uu____5273))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____5283 -> (match (uu____5283) with
| (a, uu____5287) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____5295 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____5309 -> (match (uu____5309) with
| (x, uu____5315) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5295), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____5322 = (is_fstar_value body1)
in (not (uu____5322)))
end
| uu____5323 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____5330 -> begin
rest_args
end)
in (

let body2 = (match (rest_args1) with
| [] -> begin
body1
end
| uu____5332 -> begin
(FStar_Syntax_Util.abs rest_args1 body1 copt)
end)
in ((lbname_), (f_e), (((t2), (((targs), (polytype))))), (add_unit), (body2)))))))))
end))
end
| uu____5366 -> begin
(failwith "Not enough type binders")
end)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____5376) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5385 -> (match (uu____5385) with
| (a, uu____5389) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5397 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5408 -> (match (uu____5408) with
| (x, uu____5414) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5397), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5423 -> (match (uu____5423) with
| (bv, uu____5427) -> begin
(

let uu____5428 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5428 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5462) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5467 -> (match (uu____5467) with
| (a, uu____5471) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5479 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5490 -> (match (uu____5490) with
| (x, uu____5496) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5479), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5505 -> (match (uu____5505) with
| (bv, uu____5509) -> begin
(

let uu____5510 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5510 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| FStar_Syntax_Syntax.Tm_name (uu____5544) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5549 -> (match (uu____5549) with
| (a, uu____5553) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a FStar_Pervasives_Native.None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5561 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5572 -> (match (uu____5572) with
| (x, uu____5578) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5561), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5587 -> (match (uu____5587) with
| (bv, uu____5591) -> begin
(

let uu____5592 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5592 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____5626 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____5636 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____5693 -> (match (uu____5693) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____5764 -> (match (uu____5764) with
| (a, uu____5768) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a FStar_Pervasives_Native.None)
end)) env targs)
in (

let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((FStar_Pervasives_Native.snd polytype))))
end
| uu____5770 -> begin
(FStar_Pervasives_Native.snd polytype)
end)
in (

let uu____5771 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____5771) with
| (e1, uu____5777) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____5812 = (FStar_List.fold_right (fun lb uu____5851 -> (match (uu____5851) with
| (env, lbs4) -> begin
(

let uu____5915 = lb
in (match (uu____5915) with
| (lbname, uu____5940, (t1, (uu____5942, polytype)), add_unit, uu____5945) -> begin
(

let uu____5952 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____5952) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____5812) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____6056 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____6095 = (term_as_mlexpr env_body e'1)
in (match (uu____6095) with
| (e'2, f', t') -> begin
(

let f = (

let uu____6106 = (

let uu____6108 = (FStar_List.map FStar_Pervasives_Native.fst lbs5)
in (f')::uu____6108)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____6106))
in (

let is_rec1 = (match ((is_rec = true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____6113 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____6114 = (

let uu____6115 = (

let uu____6116 = (

let uu____6117 = (FStar_List.map FStar_Pervasives_Native.snd lbs5)
in ((is_rec1), ([]), (uu____6117)))
in (mk_MLE_Let top_level uu____6116 e'2))
in (

let uu____6123 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____6115 uu____6123)))
in ((uu____6114), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____6152 = (term_as_mlexpr g scrutinee)
in (match (uu____6152) with
| (e, f_e, t_e) -> begin
(

let uu____6162 = (check_pats_for_ite pats)
in (match (uu____6162) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (FStar_Pervasives_Native.Some (then_e1), FStar_Pervasives_Native.Some (else_e1)) -> begin
(

let uu____6197 = (term_as_mlexpr g then_e1)
in (match (uu____6197) with
| (then_mle, f_then, t_then) -> begin
(

let uu____6207 = (term_as_mlexpr g else_e1)
in (match (uu____6207) with
| (else_mle, f_else, t_else) -> begin
(

let uu____6217 = (

let uu____6224 = (type_leq g t_then t_else)
in (match (uu____6224) with
| true -> begin
((t_else), (no_lift))
end
| uu____6235 -> begin
(

let uu____6236 = (type_leq g t_else t_then)
in (match (uu____6236) with
| true -> begin
((t_then), (no_lift))
end
| uu____6247 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____6217) with
| (t_branch, maybe_lift1) -> begin
(

let uu____6265 = (

let uu____6266 = (

let uu____6267 = (

let uu____6272 = (maybe_lift1 then_mle t_then)
in (

let uu____6273 = (

let uu____6275 = (maybe_lift1 else_mle t_else)
in FStar_Pervasives_Native.Some (uu____6275))
in ((e), (uu____6272), (uu____6273))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____6267))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____6266))
in (

let uu____6277 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____6265), (uu____6277), (t_branch))))
end))
end))
end))
end
| uu____6278 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____6286 -> begin
(

let uu____6287 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____6337 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____6337) with
| (pat, when_opt, branch1) -> begin
(

let uu____6367 = (extract_pat g pat t_e)
in (match (uu____6367) with
| (env, p, pat_t_compat) -> begin
(

let uu____6398 = (match (when_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____6413 = (term_as_mlexpr env w)
in (match (uu____6413) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((FStar_Pervasives_Native.Some (w2)), (f_w)))
end))
end)
in (match (uu____6398) with
| (when_opt1, f_when) -> begin
(

let uu____6441 = (term_as_mlexpr env branch1)
in (match (uu____6441) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____6460 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6497 -> (match (uu____6497) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____6460)))
end))
end))
end))
end))) true))
in (match (uu____6287) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____6581 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____6583 -> (

let uu____6584 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____6585 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____6584 uu____6585)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____6598 = (

let uu____6603 = (

let uu____6612 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____6612))
in (FStar_All.pipe_left FStar_Util.right uu____6603))
in (match (uu____6598) with
| (uu____6634, fw, uu____6636, uu____6637) -> begin
(

let uu____6638 = (

let uu____6639 = (

let uu____6640 = (

let uu____6644 = (

let uu____6646 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____6646)::[])
in ((fw), (uu____6644)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6640))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____6639))
in ((uu____6638), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____6648, uu____6649, (uu____6650, f_first, t_first)))::rest -> begin
(

let uu____6682 = (FStar_List.fold_left (fun uu____6698 uu____6699 -> (match (((uu____6698), (uu____6699))) with
| ((topt, f), (uu____6729, uu____6730, (uu____6731, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____6762 = (type_leq g t1 t_branch)
in (match (uu____6762) with
| true -> begin
FStar_Pervasives_Native.Some (t_branch)
end
| uu____6764 -> begin
(

let uu____6765 = (type_leq g t_branch t1)
in (match (uu____6765) with
| true -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____6767 -> begin
FStar_Pervasives_Native.None
end))
end))
end)
in ((topt1), (f1))))
end)) ((FStar_Pervasives_Native.Some (t_first)), (f_first)) rest)
in (match (uu____6682) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____6811 -> (match (uu____6811) with
| (p, (wopt, uu____6827), (b1, uu____6829, t1)) -> begin
(

let b2 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| FStar_Pervasives_Native.Some (uu____6840) -> begin
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

let uu____6844 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____6844), (f_match), (t_match)))))
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

let uu____6862 = (FStar_ST.read c)
in ((x), (uu____6862)));
)))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____6874 = (

let uu____6877 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6877))
in (match (uu____6874) with
| (uu____6890, fstar_disc_type) -> begin
(

let wildcards = (

let uu____6898 = (

let uu____6899 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____6899.FStar_Syntax_Syntax.n)
in (match (uu____6898) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____6908) -> begin
(

let uu____6919 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___140_6934 -> (match (uu___140_6934) with
| (uu____6938, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6939))) -> begin
true
end
| uu____6941 -> begin
false
end))))
in (FStar_All.pipe_right uu____6919 (FStar_List.map (fun uu____6961 -> (

let uu____6965 = (fresh "_")
in ((uu____6965), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____6970 -> begin
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

let uu____6982 = (

let uu____6983 = (

let uu____6989 = (

let uu____6990 = (

let uu____6991 = (

let uu____6999 = (

let uu____7000 = (

let uu____7001 = (

let uu____7002 = (FStar_Extraction_ML_Syntax.idsym mlid)
in (([]), (uu____7002)))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____7001))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) uu____7000))
in (

let uu____7004 = (

let uu____7010 = (

let uu____7015 = (

let uu____7016 = (

let uu____7020 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____7020), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____7016))
in (

let uu____7022 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____7015), (FStar_Pervasives_Native.None), (uu____7022))))
in (

let uu____7024 = (

let uu____7030 = (

let uu____7035 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____7035)))
in (uu____7030)::[])
in (uu____7010)::uu____7024))
in ((uu____6999), (uu____7004))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____6991))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6990))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____6989)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____6983))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6982))
in (

let uu____7073 = (

let uu____7074 = (

let uu____7076 = (

let uu____7077 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____7077; FStar_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____7076)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____7074)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____7073)))))))
end)))




