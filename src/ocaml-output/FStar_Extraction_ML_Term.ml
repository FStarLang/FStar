
open Prims
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____4 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


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

let uu____125 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
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
| Some (l1) -> begin
l1
end
| None -> begin
(

let res = (

let uu____238 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____238) with
| None -> begin
l
end
| Some (uu____244, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (match ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____252 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____253 -> begin
(

let ed_opt = (FStar_TypeChecker_Env.effect_decl_opt g.FStar_Extraction_ML_UEnv.tcenv l1)
in (match (ed_opt) with
| Some (ed) -> begin
(

let uu____257 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____257) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____259 -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end
| None -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end))
end)
end)))))


let rec is_arity : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let uu____267 = (

let uu____268 = (FStar_Syntax_Subst.compress t1)
in uu____268.FStar_Syntax_Syntax.n)
in (match (uu____267) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____278) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____279, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____291) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____293 = (

let uu____294 = (FStar_Syntax_Subst.compress t2)
in uu____294.FStar_Syntax_Syntax.n)
in (match (uu____293) with
| FStar_Syntax_Syntax.Tm_fvar (uu____297) -> begin
false
end
| uu____298 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____299) -> begin
(

let uu____309 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____309) with
| (head1, uu____320) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____336) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____342) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_abs (_, body, _)) | (FStar_Syntax_Syntax.Tm_let (_, body)) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____371, branches) -> begin
(match (branches) with
| ((uu____399, uu____400, e))::uu____402 -> begin
(is_arity env e)
end
| uu____438 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____458 = (

let uu____459 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____459))
in (failwith uu____458))
end
| FStar_Syntax_Syntax.Tm_constant (uu____460) -> begin
false
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____466 = (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____466) with
| true -> begin
true
end
| uu____471 -> begin
(

let uu____472 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____472) with
| ((uu____481, t2), uu____483) -> begin
(is_arity env t2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t2)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2})) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____505, uu____506) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____536) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____541, body, uu____543) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____566, body) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____578, branches) -> begin
(match (branches) with
| ((uu____606, uu____607, e))::uu____609 -> begin
(is_type_aux env e)
end
| uu____645 -> begin
(failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____658) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____664) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____687 -> (match (b) with
| true -> begin
(

let uu____688 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____689 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____688 uu____689)))
end
| uu____690 -> begin
(

let uu____691 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____692 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____691 uu____692)))
end)));
b;
)))


let is_type_binder = (fun env x -> (is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____712 = (

let uu____713 = (FStar_Syntax_Subst.compress t)
in uu____713.FStar_Syntax_Syntax.n)
in (match (uu____712) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| uu____721 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____725 = (

let uu____726 = (FStar_Syntax_Subst.compress t)
in uu____726.FStar_Syntax_Syntax.n)
in (match (uu____725) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____749 = (is_constructor head1)
in (match (uu____749) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____757 -> (match (uu____757) with
| (te, uu____761) -> begin
(is_fstar_value te)
end))))
end
| uu____762 -> begin
false
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t1, _, _)) -> begin
(is_fstar_value t1)
end
| uu____787 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____800, fields) -> begin
(FStar_Util.for_all (fun uu____812 -> (match (uu____812) with
| (uu____815, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| uu____817 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____877 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____879 = (FStar_Syntax_Util.is_fun e')
in (match (uu____879) with
| true -> begin
(aux bs e' copt)
end
| uu____880 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____888 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____888))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in (match (((FStar_List.length l) <> (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____931 -> begin
(

let uu____932 = (FStar_List.hd l)
in (match (uu____932) with
| (p1, w1, e1) -> begin
(

let uu____951 = (

let uu____956 = (FStar_List.tl l)
in (FStar_List.hd uu____956))
in (match (uu____951) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| uu____995 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1038 = (erasable g f ty)
in (match (uu____1038) with
| true -> begin
(

let uu____1039 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1039) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1040 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1041 -> begin
e
end))
in ((e1), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1055 = ((type_leq_c g (Some (e)) ty1) expect)
in (match (uu____1055) with
| (true, Some (e')) -> begin
e'
end
| uu____1061 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1066 -> (

let uu____1067 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1068 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1069 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1067 uu____1068 uu____1069))))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1076 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1076) with
| FStar_Util.Inl (uu____1077, t) -> begin
t
end
| uu____1085 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1119 = ((fun t1 -> (match (t1) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1121) -> begin
(

let uu____1125 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____1125) with
| None -> begin
false
end
| Some (t2) -> begin
((

let rec is_top_ty = (fun t3 -> (match (t3) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1132) -> begin
(

let uu____1136 = (FStar_Extraction_ML_Util.udelta_unfold g t3)
in (match (uu____1136) with
| None -> begin
false
end
| Some (t4) -> begin
(is_top_ty t4)
end))
end
| uu____1139 -> begin
false
end))
in is_top_ty) t2)
end))
end
| uu____1140 -> begin
false
end)) mlt)
in (match (uu____1119) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1142 -> begin
mlt
end)))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1148 = (

let uu____1149 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1149))
in (failwith uu____1148))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1150) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1151) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| (FStar_Syntax_Syntax.Tm_meta (t2, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2}, _)) | (FStar_Syntax_Syntax.Tm_uinst (t2, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t2, _, _)) -> begin
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

let uu____1214 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1214) with
| (bs1, c1) -> begin
(

let uu____1219 = (binders_as_ml_binders env bs1)
in (match (uu____1219) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (

let uu____1236 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____1236) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____1240 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____1242 = (FStar_List.fold_right (fun uu____1249 uu____1250 -> (match (((uu____1249), (uu____1250))) with
| ((uu____1261, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____1242) with
| (uu____1269, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____1288 = (

let uu____1289 = (FStar_Syntax_Util.un_uinst head1)
in uu____1289.FStar_Syntax_Syntax.n)
in (match (uu____1288) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____1310 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____1310))
end
| uu____1326 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____1329) -> begin
(

let uu____1352 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____1352) with
| (bs1, ty1) -> begin
(

let uu____1357 = (binders_as_ml_binders env bs1)
in (match (uu____1357) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____1375 -> (match (uu____1375) with
| (a, uu____1379) -> begin
(

let uu____1380 = (is_type g a)
in (match (uu____1380) with
| true -> begin
(term_as_mlty' g a)
end
| uu____1381 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____1385 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (uu____1385) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____1429 = (FStar_Util.first_N n_args formals)
in (match (uu____1429) with
| (uu____1443, rest) -> begin
(

let uu____1457 = (FStar_List.map (fun uu____1461 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____1457))
end))
end
| uu____1464 -> begin
mlargs
end))
in (

let nm = (

let uu____1466 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____1466) with
| Some (p) -> begin
p
end
| None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____1481 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1505 b -> (match (uu____1505) with
| (ml_bs, env) -> begin
(

let uu____1535 = (is_type_binder g b)
in (match (uu____1535) with
| true -> begin
(

let b1 = (Prims.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____1550 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____1550), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____1564 -> begin
(

let b1 = (Prims.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____1567 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____1567) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____1585 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____1585), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____1481) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____1645) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____1647, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____1650 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(match ((body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr)) with
| true -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1670 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1672 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____1673 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____1674 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____1676 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____1690 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____1706 -> begin
p
end)
end)
end
| uu____1708 -> begin
p
end))


let rec extract_one_pat : Prims.bool  ->  Prims.bool  ->  FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.list) Prims.option * Prims.bool) = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(

let ok = (type_leq g t t')
in ((match ((not (ok))) with
| true -> begin
(FStar_Extraction_ML_UEnv.debug g (fun uu____1747 -> (

let uu____1748 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____1749 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____1748 uu____1749)))))
end
| uu____1750 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____1758) -> begin
(failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____1783 = (

let uu____1784 = (

let uu____1788 = (

let uu____1790 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____1791 = (

let uu____1793 = (

let uu____1794 = (

let uu____1795 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_31)) uu____1795))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____1794))
in (uu____1793)::[])
in (uu____1790)::uu____1791))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____1788)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1784))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1783))
in (

let uu____1797 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____1797))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____1809 = (

let uu____1814 = (

let uu____1818 = (

let uu____1819 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____1819))
in ((uu____1818), ([])))
in Some (uu____1814))
in (

let uu____1824 = (ok mlty)
in ((g), (uu____1809), (uu____1824))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____1840 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____1840) with
| (g1, x1) -> begin
(

let uu____1853 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
None
end
| uu____1865 -> begin
Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____1853)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____1870) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____1894 = (

let uu____1897 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____1897) with
| FStar_Util.Inr (uu____1900, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____1902; FStar_Extraction_ML_Syntax.loc = uu____1903}, ttys, uu____1905) -> begin
((n1), (ttys))
end
| uu____1912 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____1894) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let uu____1926 = (FStar_Util.first_N nTyVars pats)
in (match (uu____1926) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____2000 -> (match (uu____2000) with
| (p1, uu____2006) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2011, t) -> begin
(term_as_mlty g t)
end
| uu____2017 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2019 -> (

let uu____2020 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____2020))));
(Prims.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____2022 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in Some (uu____2022))))
end)
with
| Un_extractable -> begin
None
end
in (

let uu____2037 = (FStar_Util.fold_map (fun g1 uu____2052 -> (match (uu____2052) with
| (p1, imp1) -> begin
(

let uu____2063 = (extract_one_pat disjunctive_pat true g1 p1 None)
in (match (uu____2063) with
| (g2, p2, uu____2079) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____2037) with
| (g1, tyMLPats) -> begin
(

let uu____2111 = (FStar_Util.fold_map (fun uu____2137 uu____2138 -> (match (((uu____2137), (uu____2138))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____2187 = (match (f_ty_opt1) with
| Some ((hd1)::rest, res) -> begin
((Some (((rest), (res)))), (Some (hd1)))
end
| uu____2219 -> begin
((None), (None))
end)
in (match (uu____2187) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____2256 = (extract_one_pat disjunctive_pat false g2 p1 expected_ty)
in (match (uu____2256) with
| (g3, p2, uu____2278) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____2111) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____2339 = (

let uu____2345 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___138_2370 -> (match (uu___138_2370) with
| Some (x) -> begin
(x)::[]
end
| uu____2392 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2345 FStar_List.split))
in (match (uu____2339) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| Some ([], t) -> begin
(ok t)
end
| uu____2431 -> begin
false
end)
in (

let uu____2436 = (

let uu____2441 = (

let uu____2445 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____2447 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____2445), (uu____2447))))
in Some (uu____2441))
in ((g2), (uu____2436), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun disj g1 p1 expected_t1 -> (

let uu____2508 = (extract_one_pat disj false g1 p1 expected_t1)
in (match (uu____2508) with
| (g2, Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____2539 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd1)::tl1 -> begin
(

let uu____2564 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in Some (uu____2564))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p1)::pats) -> begin
(

let uu____2590 = (extract_one_pat1 true g p1 (Some (expected_t)))
in (match (uu____2590) with
| (g', p2, b) -> begin
(

let uu____2613 = (FStar_Util.fold_map (fun b1 p3 -> (

let uu____2625 = (extract_one_pat1 true g p3 (Some (expected_t)))
in (match (uu____2625) with
| (uu____2637, p4, b') -> begin
(((b1 && b')), (p4))
end))) b pats)
in (match (uu____2613) with
| (b1, ps) -> begin
(

let ps1 = (p2)::ps
in (

let g1 = g'
in (

let uu____2675 = (FStar_All.pipe_right ps1 (FStar_List.partition (fun uu___139_2703 -> (match (uu___139_2703) with
| (uu____2707, (uu____2708)::uu____2709) -> begin
true
end
| uu____2712 -> begin
false
end))))
in (match (uu____2675) with
| (ps_when, rest) -> begin
(

let ps2 = (FStar_All.pipe_right ps_when (FStar_List.map (fun uu____2760 -> (match (uu____2760) with
| (x, whens) -> begin
(

let uu____2771 = (mk_when_clause whens)
in ((x), (uu____2771)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g1), (ps2), (b1))
end
| rest1 -> begin
(

let uu____2801 = (

let uu____2806 = (

let uu____2810 = (

let uu____2811 = (FStar_List.map Prims.fst rest1)
in FStar_Extraction_ML_Syntax.MLP_Branch (uu____2811))
in ((uu____2810), (None)))
in (uu____2806)::ps2)
in ((g1), (uu____2801), (b1)))
end)
in res))
end))))
end))
end))
end
| uu____2825 -> begin
(

let uu____2826 = (extract_one_pat1 false g p (Some (expected_t)))
in (match (uu____2826) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end))
end))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2908, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____2911 = (

let uu____2917 = (

let uu____2922 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____2922)))
in (uu____2917)::more_args)
in (eta_args uu____2911 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____2929, uu____2930) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____2942 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2960, args), Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____2979 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____2992 = (eta_args [] residualType)
in (match (uu____2992) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____3020 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____3020))
end
| uu____3021 -> begin
(

let uu____3027 = (FStar_List.unzip eargs)
in (match (uu____3027) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____3051 = (

let uu____3052 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____3052))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____3051))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____3057 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____3059, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3062; FStar_Extraction_ML_Syntax.loc = uu____3063}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____3081 -> begin
(

let uu____3083 = (

let uu____3087 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____3087), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3083))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(

let uu____3102 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3102))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(

let uu____3108 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3108))
end
| uu____3110 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____3123 = ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____3123) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____3124 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____3164 = (term_as_mlexpr' g t)
in (match (uu____3164) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3177 = (

let uu____3178 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3179 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____3180 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____3178 uu____3179 uu____3180 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____3177))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____3187 = (check_term_as_mlexpr' g t f ty)
in (match (uu____3187) with
| (e, t1) -> begin
(

let uu____3194 = (erase g e t1 f)
in (match (uu____3194) with
| (r, uu____3201, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____3209 = (term_as_mlexpr g e0)
in (match (uu____3209) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____3221 = (maybe_coerce g e t ty)
in ((uu____3221), (ty)))
end
| uu____3222 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3232 = (

let uu____3233 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3234 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____3235 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____3233 uu____3234 uu____3235))))
in (FStar_Util.print_string uu____3232))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(

let uu____3243 = (

let uu____3244 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3244))
in (failwith uu____3243))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____3256 = (term_as_mlexpr' g t1)
in (match (uu____3256) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____3283 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____3292)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in (

let uu____3316 = (

let uu____3317 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____3317 Prims.op_Negation))
in (match (uu____3316) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____3322 -> begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____3324 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____3324) with
| (comp_1, uu____3332, uu____3333) -> begin
(

let uu____3334 = (

let k = (

let uu____3338 = (

let uu____3339 = (

let uu____3340 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right uu____3340 FStar_Syntax_Syntax.mk_binder))
in (uu____3339)::[])
in (FStar_Syntax_Util.abs uu____3338 body None))
in (

let uu____3346 = (term_as_mlexpr g k)
in (match (uu____3346) with
| (ml_k, uu____3353, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3356, uu____3357, m_2) -> begin
m_2
end
| uu____3359 -> begin
(failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (uu____3334) with
| (ml_k, ty) -> begin
(

let bind1 = (

let uu____3366 = (

let uu____3367 = (

let uu____3368 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right uu____3368 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____3367))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____3366))
in (

let uu____3373 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind1), ((comp_1)::(ml_k)::[])))))
in ((uu____3373), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)))
end
| uu____3375 -> begin
(term_as_mlexpr' g t2)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, _)) | (FStar_Syntax_Syntax.Tm_uinst (t1, _)) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3388 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____3388) with
| (uu____3395, ty, uu____3397) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____3399 = (

let uu____3400 = (

let uu____3401 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_32 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_32)) uu____3401))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3400))
in ((uu____3399), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let uu____3404 = (is_type g t)
in (match (uu____3404) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3408 -> begin
(

let uu____3409 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3409) with
| (FStar_Util.Inl (uu____3416), uu____3417) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____3436, x, mltys, uu____3439), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____3464 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____3464), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____3465 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____3494 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3494) with
| (bs1, body1) -> begin
(

let body2 = (match (copt) with
| Some (c) -> begin
(

let uu____3514 = (FStar_TypeChecker_Env.is_reifiable g.FStar_Extraction_ML_UEnv.tcenv c)
in (match (uu____3514) with
| true -> begin
(FStar_TypeChecker_Util.reify_body g.FStar_Extraction_ML_UEnv.tcenv body1)
end
| uu____3515 -> begin
body1
end))
end
| None -> begin
body1
end)
in (

let uu____3521 = (binders_as_ml_binders g bs1)
in (match (uu____3521) with
| (ml_bs, env) -> begin
(

let uu____3538 = (term_as_mlexpr env body2)
in (match (uu____3538) with
| (ml_body, f, t1) -> begin
(

let uu____3548 = (FStar_List.fold_right (fun uu____3555 uu____3556 -> (match (((uu____3555), (uu____3556))) with
| ((uu____3567, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____3548) with
| (f1, tfun) -> begin
(

let uu____3580 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____3580), (f1), (tfun)))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____3584; FStar_Syntax_Syntax.pos = uu____3585; FStar_Syntax_Syntax.vars = uu____3586}, (t1)::[]) -> begin
(

let uu____3609 = (term_as_mlexpr' g (Prims.fst t1))
in (match (uu____3609) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3621)); FStar_Syntax_Syntax.tk = uu____3622; FStar_Syntax_Syntax.pos = uu____3623; FStar_Syntax_Syntax.vars = uu____3624}, (t1)::[]) -> begin
(

let uu____3647 = (term_as_mlexpr' g (Prims.fst t1))
in (match (uu____3647) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun uu___141_3683 -> (match (uu___141_3683) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l, flags) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right flags (FStar_List.existsb (fun uu___140_3701 -> (match (uu___140_3701) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3702 -> begin
false
end)))))
end))
in (

let uu____3703 = (

let uu____3706 = (

let uu____3707 = (FStar_Syntax_Subst.compress head1)
in uu____3707.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____3706)))
in (match (uu____3703) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____3713), uu____3714) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____3724, FStar_Syntax_Syntax.Tm_abs (bs, uu____3726, Some (lc))) when (is_total lc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| uu____3755 -> begin
(

let rec extract_app = (fun is_data uu____3783 uu____3784 restArgs -> (match (((uu____3783), (uu____3784))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____3832) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____3846 -> begin
false
end))
in (

let uu____3847 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____3860 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (uu____3860)))
end
| uu____3876 -> begin
(FStar_List.fold_left (fun uu____3885 uu____3886 -> (match (((uu____3885), (uu____3886))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((f1 = FStar_Extraction_ML_Syntax.E_PURE) || (f1 = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____3939 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____3941 = (

let uu____3943 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____3943)::out_args)
in (((((x), (arg)))::lbs), (uu____3941))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____3847) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____3970 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____3970))
in (

let l_app = (FStar_List.fold_right (fun uu____3975 out -> (match (uu____3975) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____3988))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when ((is_type g arg) && (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)) -> begin
(

let uu____4006 = (

let uu____4009 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____4009), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____4006 rest))
end
| (((e0, uu____4016))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____4035 = (term_as_mlexpr g e0)
in (match (uu____4035) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____4046 = (

let uu____4049 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____4049), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____4046 rest)))
end)))
end
| uu____4055 -> begin
(

let uu____4062 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____4062) with
| Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____4098 args1 -> (match (uu____4098) with
| (f, t1) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (uu____4117)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (uu____4167))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4169, f', t3)) -> begin
(

let uu____4194 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____4194 t3))
end
| uu____4195 -> begin
((args2), (f1), (t2))
end))
in (

let uu____4210 = (remove_implicits args1 f t1)
in (match (uu____4210) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____4243 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____4250 = (is_type g t)
in (match (uu____4250) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____4254 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let uu____4261 = (

let uu____4268 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____4268) with
| (FStar_Util.Inr (uu____4278, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____4303 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4261) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4332))::uu____4333 -> begin
(is_type g a)
end
| uu____4347 -> begin
false
end)
in (

let uu____4353 = (match (vars) with
| (uu____4370)::uu____4371 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____4378 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____4398 = (FStar_Util.first_N n1 args)
in (match (uu____4398) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4451 -> (match (uu____4451) with
| (x, uu____4455) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let uu___145_4460 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___145_4460.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___145_4460.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4462; FStar_Extraction_ML_Syntax.loc = uu____4463})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___146_4466 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___146_4466.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___146_4466.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____4467 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____4473 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____4353) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____4505 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____4505), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____4506 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____4512 -> begin
(

let uu____4513 = (term_as_mlexpr g head2)
in (match (uu____4513) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____4525), f) -> begin
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
| None -> begin
(failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let uu____4579 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____4579) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____4600 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____4607 -> begin
(

let uu____4608 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4608) with
| true -> begin
((lbs), (e'))
end
| uu____4615 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____4618 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____4618))
in (

let lb1 = (

let uu___147_4620 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___147_4620.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___147_4620.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___147_4620.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___147_4620.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____4600) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____4637 = (FStar_Ident.lid_of_path (FStar_List.append (Prims.fst g.FStar_Extraction_ML_UEnv.currentModule) (((Prims.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____4637))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____4641 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____4645 = (FStar_Options.ml_ish ())
in (match (uu____4645) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____4648 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___148_4649 = lb
in {FStar_Syntax_Syntax.lbname = uu___148_4649.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___148_4649.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___148_4649.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___148_4649.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____4650 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____4663 -> (match (uu____4663) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____4674; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____4717 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____4717 (is_type_binder g))) -> begin
(

let uu____4724 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4724) with
| (bs1, c1) -> begin
(

let uu____4738 = (

let uu____4743 = (FStar_Util.prefix_until (fun x -> (

let uu____4761 = (is_type_binder g x)
in (not (uu____4761)))) bs1)
in (match (uu____4743) with
| None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| Some (bs2, b, rest) -> begin
(

let uu____4809 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____4809)))
end))
in (match (uu____4738) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____4839 = (normalize_abs e)
in (FStar_All.pipe_right uu____4839 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, uu____4851) -> begin
(

let uu____4874 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____4874) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____4904 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____4904) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____4947 uu____4948 -> (match (((uu____4947), (uu____4948))) with
| ((x, uu____4958), (y, uu____4960)) -> begin
(

let uu____4965 = (

let uu____4970 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____4970)))
in FStar_Syntax_Syntax.NT (uu____4965))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____4975 -> (match (uu____4975) with
| (a, uu____4979) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____4987 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____5001 -> (match (uu____5001) with
| (x, uu____5007) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____4987), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____5014 = (is_fstar_value body1)
in (not (uu____5014)))
end
| uu____5015 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____5022 -> begin
rest_args
end)
in (

let body2 = (match (rest_args1) with
| [] -> begin
body1
end
| uu____5024 -> begin
(FStar_Syntax_Util.abs rest_args1 body1 None)
end)
in ((lbname_), (f_e), (((t2), (((targs), (polytype))))), (add_unit), (body2)))))))))
end))
end
| uu____5063 -> begin
(failwith "Not enough type binders")
end)
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5080 -> (match (uu____5080) with
| (a, uu____5084) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5092 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5103 -> (match (uu____5103) with
| (x, uu____5109) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5092), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5118 -> (match (uu____5118) with
| (bv, uu____5122) -> begin
(

let uu____5123 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5123 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args))))) None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____5161 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____5171 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____5228 -> (match (uu____5228) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____5299 -> (match (uu____5299) with
| (a, uu____5303) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a None)
end)) env targs)
in (

let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end
| uu____5305 -> begin
(Prims.snd polytype)
end)
in (

let uu____5306 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____5306) with
| (e1, uu____5312) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____5347 = (FStar_List.fold_right (fun lb uu____5386 -> (match (uu____5386) with
| (env, lbs4) -> begin
(

let uu____5450 = lb
in (match (uu____5450) with
| (lbname, uu____5475, (t1, (uu____5477, polytype)), add_unit, uu____5480) -> begin
(

let uu____5487 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____5487) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____5347) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____5591 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____5630 = (term_as_mlexpr env_body e'1)
in (match (uu____5630) with
| (e'2, f', t') -> begin
(

let f = (

let uu____5641 = (

let uu____5643 = (FStar_List.map Prims.fst lbs5)
in (f')::uu____5643)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____5641))
in (

let is_rec1 = (match ((is_rec = true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____5648 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____5649 = (

let uu____5650 = (

let uu____5651 = (

let uu____5652 = (FStar_List.map Prims.snd lbs5)
in ((is_rec1), ([]), (uu____5652)))
in (mk_MLE_Let top_level uu____5651 e'2))
in (

let uu____5658 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____5650 uu____5658)))
in ((uu____5649), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____5687 = (term_as_mlexpr g scrutinee)
in (match (uu____5687) with
| (e, f_e, t_e) -> begin
(

let uu____5697 = (check_pats_for_ite pats)
in (match (uu____5697) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (Some (then_e1), Some (else_e1)) -> begin
(

let uu____5732 = (term_as_mlexpr g then_e1)
in (match (uu____5732) with
| (then_mle, f_then, t_then) -> begin
(

let uu____5742 = (term_as_mlexpr g else_e1)
in (match (uu____5742) with
| (else_mle, f_else, t_else) -> begin
(

let uu____5752 = (

let uu____5759 = (type_leq g t_then t_else)
in (match (uu____5759) with
| true -> begin
((t_else), (no_lift))
end
| uu____5770 -> begin
(

let uu____5771 = (type_leq g t_else t_then)
in (match (uu____5771) with
| true -> begin
((t_then), (no_lift))
end
| uu____5782 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____5752) with
| (t_branch, maybe_lift1) -> begin
(

let uu____5800 = (

let uu____5801 = (

let uu____5802 = (

let uu____5807 = (maybe_lift1 then_mle t_then)
in (

let uu____5808 = (

let uu____5810 = (maybe_lift1 else_mle t_else)
in Some (uu____5810))
in ((e), (uu____5807), (uu____5808))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____5802))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____5801))
in (

let uu____5812 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____5800), (uu____5812), (t_branch))))
end))
end))
end))
end
| uu____5813 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____5821 -> begin
(

let uu____5822 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____5872 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____5872) with
| (pat, when_opt, branch1) -> begin
(

let uu____5902 = (extract_pat g pat t_e)
in (match (uu____5902) with
| (env, p, pat_t_compat) -> begin
(

let uu____5933 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let uu____5948 = (term_as_mlexpr env w)
in (match (uu____5948) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w2)), (f_w)))
end))
end)
in (match (uu____5933) with
| (when_opt1, f_when) -> begin
(

let uu____5976 = (term_as_mlexpr env branch1)
in (match (uu____5976) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____5995 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6032 -> (match (uu____6032) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____5995)))
end))
end))
end))
end))) true))
in (match (uu____5822) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____6116 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____6118 -> (

let uu____6119 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____6120 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____6119 uu____6120)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____6133 = (

let uu____6138 = (

let uu____6147 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____6147))
in (FStar_All.pipe_left FStar_Util.right uu____6138))
in (match (uu____6133) with
| (uu____6169, fw, uu____6171, uu____6172) -> begin
(

let uu____6173 = (

let uu____6174 = (

let uu____6175 = (

let uu____6179 = (

let uu____6181 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____6181)::[])
in ((fw), (uu____6179)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6175))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____6174))
in ((uu____6173), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____6183, uu____6184, (uu____6185, f_first, t_first)))::rest -> begin
(

let uu____6217 = (FStar_List.fold_left (fun uu____6233 uu____6234 -> (match (((uu____6233), (uu____6234))) with
| ((topt, f), (uu____6264, uu____6265, (uu____6266, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| None -> begin
None
end
| Some (t1) -> begin
(

let uu____6297 = (type_leq g t1 t_branch)
in (match (uu____6297) with
| true -> begin
Some (t_branch)
end
| uu____6299 -> begin
(

let uu____6300 = (type_leq g t_branch t1)
in (match (uu____6300) with
| true -> begin
Some (t1)
end
| uu____6302 -> begin
None
end))
end))
end)
in ((topt1), (f1))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (uu____6217) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____6346 -> (match (uu____6346) with
| (p, (wopt, uu____6362), (b1, uu____6364, t1)) -> begin
(

let b2 = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| Some (uu____6375) -> begin
b1
end)
in ((p), (wopt), (b2)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t1) -> begin
t1
end)
in (

let uu____6379 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____6379), (f_match), (t_match)))))
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

let uu____6397 = (FStar_ST.read c)
in ((x), (uu____6397)));
)))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____6409 = (

let uu____6412 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left Prims.fst uu____6412))
in (match (uu____6409) with
| (uu____6425, fstar_disc_type) -> begin
(

let wildcards = (

let uu____6433 = (

let uu____6434 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____6434.FStar_Syntax_Syntax.n)
in (match (uu____6433) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____6443) -> begin
(

let uu____6454 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___142_6469 -> (match (uu___142_6469) with
| (uu____6473, Some (FStar_Syntax_Syntax.Implicit (uu____6474))) -> begin
true
end
| uu____6476 -> begin
false
end))))
in (FStar_All.pipe_right uu____6454 (FStar_List.map (fun uu____6496 -> (

let uu____6500 = (fresh "_")
in ((uu____6500), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____6505 -> begin
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

let uu____6517 = (

let uu____6518 = (

let uu____6524 = (

let uu____6525 = (

let uu____6526 = (

let uu____6534 = (

let uu____6535 = (

let uu____6536 = (

let uu____6537 = (FStar_Extraction_ML_Syntax.idsym mlid)
in (([]), (uu____6537)))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____6536))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) uu____6535))
in (

let uu____6539 = (

let uu____6545 = (

let uu____6550 = (

let uu____6551 = (

let uu____6555 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____6555), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____6551))
in (

let uu____6557 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____6550), (None), (uu____6557))))
in (

let uu____6559 = (

let uu____6565 = (

let uu____6570 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (uu____6570)))
in (uu____6565)::[])
in (uu____6545)::uu____6559))
in ((uu____6534), (uu____6539))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____6526))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6525))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____6524)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____6518))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6517))
in (

let uu____6608 = (

let uu____6609 = (

let uu____6611 = (

let uu____6612 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____6612; FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____6611)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____6609)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____6608)))))))
end)))




