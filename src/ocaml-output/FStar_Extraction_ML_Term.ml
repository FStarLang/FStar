
open Prims

exception Un_extractable


let is_Un_extractable = (fun _discr_ -> (match (_discr_) with
| Un_extractable (_) -> begin
true
end
| _ -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail = (fun r msg -> (

let _79_23 = (let _174_33 = (let _174_32 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _174_32 msg))
in (FStar_All.pipe_left FStar_Util.print_string _174_33))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _79_29 -> (match (_79_29) with
| (vars, ty) -> begin
(let _174_41 = (let _174_40 = (FStar_Syntax_Print.term_to_string t)
in (let _174_39 = (let _174_37 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _174_37 (FStar_String.concat ", ")))
in (let _174_38 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _174_40 _174_39 _174_38))))
in (fail t.FStar_Syntax_Syntax.pos _174_41))
end))


let err_ill_typed_application = (fun env t args ty -> (let _174_51 = (let _174_50 = (FStar_Syntax_Print.term_to_string t)
in (let _174_49 = (let _174_47 = (FStar_All.pipe_right args (FStar_List.map (fun _79_37 -> (match (_79_37) with
| (x, _79_36) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _174_47 (FStar_String.concat " ")))
in (let _174_48 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _174_50 _174_49 _174_48))))
in (fail t.FStar_Syntax_Syntax.pos _174_51)))


let err_value_restriction = (fun t -> (let _174_55 = (let _174_54 = (FStar_Syntax_Print.tag_of_term t)
in (let _174_53 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _174_54 _174_53)))
in (fail t.FStar_Syntax_Syntax.pos _174_55)))


let err_unexpected_eff = (fun t f0 f1 -> (let _174_60 = (let _174_59 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _174_59 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _174_60)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)) with
| None -> begin
l
end
| Some (_79_51, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _79_56 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in (fun g l -> (

let l = (delta_norm_eff g l)
in if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))))


type level_t =
| Term_level
| Type_level
| Kind_level


let is_Term_level = (fun _discr_ -> (match (_discr_) with
| Term_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_level = (fun _discr_ -> (match (_discr_) with
| Kind_level (_) -> begin
true
end
| _ -> begin
false
end))


let predecessor = (fun t _79_1 -> (match (_79_1) with
| Term_level -> begin
Term_level
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))


let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (

let predecessor = (fun l -> (predecessor t l))
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _79_73 = (FStar_Extraction_ML_UEnv.debug env (fun _79_71 -> (let _174_82 = (FStar_Syntax_Print.term_to_string t)
in (let _174_81 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _174_82 _174_81)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_79_76) -> begin
(let _174_87 = (let _174_86 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _174_86))
in (FStar_All.failwith _174_87))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_79_80) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _79_88; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (_79_85); FStar_Syntax_Syntax.fv_qual = _79_83}) -> begin
(

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let _79_93 = (FStar_Extraction_ML_UEnv.debug env (fun _79_92 -> (match (()) with
| () -> begin
(let _174_90 = (FStar_Syntax_Print.term_to_string t)
in (let _174_89 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _174_90 _174_89)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _174_91 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _174_91))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _174_92 = (level env t)
in (FStar_All.pipe_left predecessor _174_92))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _79_116, _79_118) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_79_122) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _79_126) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _79_131) -> begin
(match ((level env x.FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((level env (FStar_Syntax_Util.comp_result c))) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_145) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_79_149, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_79_154, branches) -> begin
(match (branches) with
| ((_79_161, _79_163, e))::_79_159 -> begin
(level env e)
end
| _79_168 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _79_171) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _79_176) -> begin
(level env head)
end)))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _79_183 -> begin
true
end))


let is_type_binder = (fun env x -> (match ((level env (Prims.fst x).FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
(FStar_All.failwith "Impossible: Binder is a term")
end
| Type_level -> begin
false
end
| Kind_level -> begin
true
end))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _174_101 = (FStar_Syntax_Subst.compress t)
in _174_101.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _79_209 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _174_104 = (FStar_Syntax_Subst.compress t)
in _174_104.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_230 -> (match (_79_230) with
| (te, _79_229) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _79_243 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_264, fields) -> begin
(FStar_Util.for_all (fun _79_271 -> (match (_79_271) with
| (_79_269, e) -> begin
(is_ml_value e)
end)) fields)
end
| _79_273 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _79_286 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _174_117 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _174_117))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _79_293 = (FStar_List.hd l)
in (match (_79_293) with
| (p1, w1, e1) -> begin
(

let _79_297 = (let _174_120 = (FStar_List.tl l)
in (FStar_List.hd _174_120))
in (match (_79_297) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _79_317 -> begin
def
end)
end))
end))
end))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e = if (erasable g f ty) then begin
if (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end
end else begin
e
end
in ((e), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _79_338 -> begin
(

let _79_340 = (FStar_Extraction_ML_UEnv.debug g (fun _79_339 -> (match (()) with
| () -> begin
(let _174_150 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _174_149 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _174_148 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _174_150 _174_149 _174_148))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect))))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_79_345, t) -> begin
t
end
| _79_350 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_357) -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| None -> begin
false
end
| Some (t) -> begin
(is_top_ty t)
end)
end
| _79_363 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in if (is_top_ty mlt) then begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t))
end else begin
mlt
end))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _174_173 = (let _174_172 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _174_172))
in (FStar_All.failwith _174_173))
end
| FStar_Syntax_Syntax.Tm_constant (_79_378) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (_79_381) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(term_as_mlty' env t)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv [])
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _79_417 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_417) with
| (bs, c) -> begin
(

let _79_420 = (binders_as_ml_binders env bs)
in (match (_79_420) with
| (mlbs, env) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env.FStar_Extraction_ML_UEnv.tcenv eff)
in if (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) then begin
(

let t = (FStar_TypeChecker_Util.reify_comp env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.lcomp_of_comp c) FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env t)
in res))
end else begin
(term_as_mlty' env (FStar_Syntax_Util.comp_result c))
end))
in (

let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (

let _79_437 = (FStar_List.fold_right (fun _79_430 _79_433 -> (match (((_79_430), (_79_433))) with
| ((_79_428, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (_79_437) with
| (_79_435, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _174_176 = (FStar_Syntax_Util.un_uinst head)
in _174_176.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _174_177 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _174_177))
end
| _79_451 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _79_456) -> begin
(

let _79_461 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_79_461) with
| (bs, ty) -> begin
(

let _79_464 = (binders_as_ml_binders env bs)
in (match (_79_464) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _79_478 -> (match (_79_478) with
| (a, _79_477) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _79_484 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_79_484) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _79_490 = (FStar_Util.first_N n_args formals)
in (match (_79_490) with
| (_79_488, rest) -> begin
(let _174_184 = (FStar_List.map (fun _79_491 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _174_184))
end))
end else begin
mlargs
end)
in (

let nm = (match ((FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)) with
| Some (p) -> begin
p
end
| None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _79_513 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _79_502 b -> (match (_79_502) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _174_189 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_174_189), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _174_190 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_174_190), (t)))
in (((ml_b)::ml_bs), (env))))))
end
end)) (([]), (g))))
in (match (_79_513) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _79_524) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_79_527, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _79_532 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _79_548 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _79_550 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _79_552 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| _79_554 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _79_564 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| _79_573 -> begin
p
end)
end)
end
| _79_575 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(

let ok = (type_leq g t t')
in (

let _79_593 = if (not (ok)) then begin
(FStar_Extraction_ML_UEnv.debug g (fun _79_591 -> (let _174_225 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (let _174_224 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" _174_225 _174_224)))))
end else begin
()
end
in ok))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_79_596) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _174_234 = (let _174_233 = (let _174_232 = (let _174_231 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _174_230 = (let _174_229 = (let _174_228 = (let _174_227 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _174_226 -> FStar_Extraction_ML_Syntax.MLE_Const (_174_226)) _174_227))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _174_228))
in (_174_229)::[])
in (_174_231)::_174_230))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_174_232)))
in FStar_Extraction_ML_Syntax.MLE_App (_174_233))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _174_234))
in (let _174_235 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_174_235))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _174_240 = (let _174_238 = (let _174_237 = (let _174_236 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_174_236))
in ((_174_237), ([])))
in Some (_174_238))
in (let _174_239 = (ok mlty)
in ((g), (_174_240), (_174_239))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _174_245 = if imp then begin
None
end else begin
(let _174_243 = (let _174_242 = (let _174_241 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_174_241))
in ((_174_242), ([])))
in Some (_174_243))
end
in (let _174_244 = (ok mlty)
in ((g), (_174_245), (_174_244))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _174_250 = if imp then begin
None
end else begin
(let _174_248 = (let _174_247 = (let _174_246 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_174_246))
in ((_174_247), ([])))
in Some (_174_248))
end
in (let _174_249 = (ok mlty)
in ((g), (_174_250), (_174_249))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_79_621) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _79_643 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _79_630; FStar_Extraction_ML_Syntax.loc = _79_628}, ttys, _79_636) -> begin
((n), (ttys))
end
| _79_640 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_79_643) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _79_647 = (FStar_Util.first_N nTyVars pats)
in (match (_79_647) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _79_657 -> (match (_79_657) with
| (p, _79_656) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_79_659, t) -> begin
(term_as_mlty g t)
end
| _79_664 -> begin
(

let _79_667 = (FStar_Extraction_ML_UEnv.debug g (fun _79_665 -> (let _174_254 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s is not extractable" _174_254))))
in (Prims.raise Un_extractable))
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (let _174_255 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in Some (_174_255))))
end)
with
| Un_extractable -> begin
None
end
in (

let _79_683 = (FStar_Util.fold_map (fun g _79_675 -> (match (_79_675) with
| (p, imp) -> begin
(

let _79_680 = (extract_one_pat disjunctive_pat true g p None)
in (match (_79_680) with
| (g, p, _79_679) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (_79_683) with
| (g, tyMLPats) -> begin
(

let _79_710 = (FStar_Util.fold_map (fun _79_686 _79_689 -> (match (((_79_686), (_79_689))) with
| ((g, f_ty_opt), (p, imp)) -> begin
(

let _79_700 = (match (f_ty_opt) with
| Some ((hd)::rest, res) -> begin
((Some (((rest), (res)))), (Some (hd)))
end
| _79_697 -> begin
((None), (None))
end)
in (match (_79_700) with
| (f_ty_opt, expected_ty) -> begin
(

let _79_705 = (extract_one_pat disjunctive_pat false g p expected_ty)
in (match (_79_705) with
| (g, p, _79_704) -> begin
((((g), (f_ty_opt))), (p))
end))
end))
end)) ((g), (f_ty_opt)) restPats)
in (match (_79_710) with
| ((g, f_ty_opt), restMLPats) -> begin
(

let _79_718 = (let _174_262 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| Some (x) -> begin
(x)::[]
end
| _79_715 -> begin
[]
end))))
in (FStar_All.pipe_right _174_262 FStar_List.split))
in (match (_79_718) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt) with
| Some ([], t) -> begin
(ok t)
end
| _79_724 -> begin
false
end)
in (let _174_266 = (let _174_265 = (let _174_264 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _174_263 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_174_264), (_174_263))))
in Some (_174_265))
in ((g), (_174_266), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))
in (

let extract_one_pat = (fun disj g p expected_t -> (match ((extract_one_pat disj false g p expected_t)) with
| (g, Some (x, v), b) -> begin
((g), (((x), (v))), (b))
end
| _79_739 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _174_277 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_174_277))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _79_755 = (extract_one_pat true g p (Some (expected_t)))
in (match (_79_755) with
| (g, p, b) -> begin
(

let _79_765 = (FStar_Util.fold_map (fun b p -> (

let _79_762 = (extract_one_pat true g p (Some (expected_t)))
in (match (_79_762) with
| (_79_759, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (_79_765) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _79_780 = (FStar_All.pipe_right ps (FStar_List.partition (fun _79_3 -> (match (_79_3) with
| (_79_769, (_79_773)::_79_771) -> begin
true
end
| _79_777 -> begin
false
end))))
in (match (_79_780) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _79_783 -> (match (_79_783) with
| (x, whens) -> begin
(let _174_282 = (mk_when_clause whens)
in ((x), (_174_282)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _174_286 = (let _174_285 = (let _174_284 = (let _174_283 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_174_283))
in ((_174_284), (None)))
in (_174_285)::ps)
in ((g), (_174_286), (b)))
end)
in res))
end)))
end))
end))
end
| _79_789 -> begin
(

let _79_795 = (extract_one_pat false g p (Some (expected_t)))
in (match (_79_795) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _79_806, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _174_301 = (let _174_300 = (let _174_299 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_174_299)))
in (_174_300)::more_args)
in (eta_args _174_301 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_812, _79_814) -> begin
(((FStar_List.rev more_args)), (t))
end
| _79_818 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_79_823, args), Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _79_836 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _79_842 = (eta_args [] residualType)
in (match (_79_842) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _174_310 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _174_310))
end
| _79_845 -> begin
(

let _79_848 = (FStar_List.unzip eargs)
in (match (_79_848) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _174_312 = (let _174_311 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _174_311))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _174_312))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _79_855 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (_79_857, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _79_863; FStar_Extraction_ML_Syntax.loc = _79_861}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
(

let f = (FStar_Ident.lid_of_ids (FStar_List.append constrname.FStar_Ident.ns ((f)::[])))
in (

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _79_883 -> begin
(let _174_314 = (let _174_313 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_174_313), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_174_314))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _174_315 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _174_315))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _174_316 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _174_316))
end
| _79_923 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _79_932 = (term_as_mlexpr' g t)
in (match (_79_932) with
| (e, tag, ty) -> begin
(

let tag = (maybe_downgrade_eff g tag ty)
in (

let _79_935 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _174_341 = (let _174_340 = (FStar_Syntax_Print.tag_of_term t)
in (let _174_339 = (FStar_Syntax_Print.term_to_string t)
in (let _174_338 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" _174_340 _174_339 _174_338 (FStar_Extraction_ML_Util.eff_to_string tag)))))
in (FStar_Util.print_string _174_341))))
in (erase g e ty tag)))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _79_943 = (check_term_as_mlexpr' g t f ty)
in (match (_79_943) with
| (e, t) -> begin
(

let _79_948 = (erase g e t f)
in (match (_79_948) with
| (r, _79_946, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _79_956 = (term_as_mlexpr g e0)
in (match (_79_956) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _174_350 = (maybe_coerce g e t ty)
in ((_174_350), (ty)))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _79_961 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _174_357 = (let _174_356 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _174_355 = (FStar_Syntax_Print.tag_of_term top)
in (let _174_354 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" _174_356 _174_355 _174_354))))
in (FStar_Util.print_string _174_357))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _174_359 = (let _174_358 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _174_358))
in (FStar_All.failwith _174_359))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| _79_1002 -> begin
(FStar_All.failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, _79_1006)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _174_360 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _174_360 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _79_1026 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_79_1026) with
| (comp_1, _79_1023, _79_1025) -> begin
(

let _79_1045 = (

let k = (let _174_363 = (let _174_362 = (let _174_361 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _174_361 FStar_Syntax_Syntax.mk_binder))
in (_174_362)::[])
in (FStar_Syntax_Util.abs _174_363 body None))
in (

let _79_1032 = (term_as_mlexpr g k)
in (match (_79_1032) with
| (ml_k, _79_1030, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_1034, _79_1036, m_2) -> begin
m_2
end
| _79_1041 -> begin
(FStar_All.failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (_79_1045) with
| (ml_k, ty) -> begin
(

let bind = (let _174_366 = (let _174_365 = (let _174_364 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _174_364 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_174_365))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _174_366))
in (let _174_367 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_174_367), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)
end
| _79_1048 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _79_1065 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_79_1065) with
| (_79_1061, ty, _79_1064) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _174_371 = (let _174_370 = (let _174_369 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _174_368 -> FStar_Extraction_ML_Syntax.MLE_Const (_174_368)) _174_369))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _174_370))
in ((_174_371), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_79_1074), _79_1077) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, _79_1082), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _174_372 = (maybe_eta_data_and_project_record g qual t x)
in ((_174_372), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _79_1094 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _79_1102 = (FStar_Syntax_Subst.open_term bs body)
in (match (_79_1102) with
| (bs, body) -> begin
(

let _79_1105 = (binders_as_ml_binders g bs)
in (match (_79_1105) with
| (ml_bs, env) -> begin
(

let _79_1109 = (term_as_mlexpr env body)
in (match (_79_1109) with
| (ml_body, f, t) -> begin
(

let _79_1119 = (FStar_List.fold_right (fun _79_1113 _79_1116 -> (match (((_79_1113), (_79_1116))) with
| ((_79_1111, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_79_1119) with
| (f, tfun) -> begin
(let _174_375 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_174_375), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _79_1125; FStar_Syntax_Syntax.pos = _79_1123; FStar_Syntax_Syntax.vars = _79_1121}, (t)::[]) -> begin
(

let _79_1136 = (term_as_mlexpr' g (Prims.fst t))
in (match (_79_1136) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_79_1144)); FStar_Syntax_Syntax.tk = _79_1142; FStar_Syntax_Syntax.pos = _79_1140; FStar_Syntax_Syntax.vars = _79_1138}, (t)::[]) -> begin
(

let _79_1155 = (term_as_mlexpr' g (Prims.fst t))
in (match (_79_1155) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_total = (fun _79_5 -> (match (_79_5) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l, flags) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right flags (FStar_List.existsb (fun _79_4 -> (match (_79_4) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _79_1170 -> begin
false
end)))))
end))
in (match ((let _174_380 = (let _174_379 = (FStar_Syntax_Subst.compress head)
in _174_379.FStar_Syntax_Syntax.n)
in ((head.FStar_Syntax_Syntax.n), (_174_380)))) with
| (FStar_Syntax_Syntax.Tm_uvar (_79_1173), _79_1176) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| (_79_1180, FStar_Syntax_Syntax.Tm_abs (bs, _79_1183, Some (lc))) when (is_total lc) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _79_1191 -> begin
(

let rec extract_app = (fun is_data _79_1196 _79_1199 restArgs -> (match (((_79_1196), (_79_1199))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _79_1203) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _79_1212; FStar_Syntax_Syntax.p = _79_1210}; FStar_Syntax_Syntax.fv_delta = _79_1208; FStar_Syntax_Syntax.fv_qual = _79_1206}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _79_1218 -> begin
false
end))
in (

let _79_1229 = if evaluation_order_guaranteed then begin
(let _174_389 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_174_389)))
end else begin
(FStar_List.fold_left (fun _79_1222 _79_1225 -> (match (((_79_1222), (_79_1225))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _174_393 = (let _174_392 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_174_392)::out_args)
in (((((x), (arg)))::lbs), (_174_393))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_79_1229) with
| (lbs, mlargs) -> begin
(

let app = (let _174_394 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _174_394))
in (

let l_app = (FStar_List.fold_right (fun _79_1233 out -> (match (_79_1233) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, _79_1239))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _174_398 = (let _174_397 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((_174_397), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _174_398 rest))
end else begin
(let _174_403 = (let _174_402 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _174_401 = (FStar_Syntax_Print.term_to_string arg)
in (let _174_400 = (FStar_Syntax_Print.tag_of_term arg)
in (let _174_399 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _174_402 _174_401 _174_400 _174_399)))))
in (FStar_All.failwith _174_403))
end
end
| (((e0, _79_1251))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let _79_1264 = (term_as_mlexpr g e0)
in (match (_79_1264) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _174_405 = (let _174_404 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((_174_404), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _174_405 rest)))
end)))
end
| _79_1267 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t)
end)
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead _79_1276 args -> (match (_79_1276) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_79_1279)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (_79_1289))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_79_1295, f', t)) -> begin
(let _174_420 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f f')
in (remove_implicits args _174_420 t))
end
| _79_1302 -> begin
((args), (f), (t))
end))
in (

let _79_1306 = (remove_implicits args f t)
in (match (_79_1306) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _79_1308 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let _79_1329 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| _79_1321 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_79_1329) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _79_1334))::_79_1331 -> begin
(is_type g a)
end
| _79_1338 -> begin
false
end)
in (

let _79_1384 = (match (vars) with
| (_79_1343)::_79_1341 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _79_1346 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _79_1350 = (FStar_Util.first_N n args)
in (match (_79_1350) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _79_1354 -> (match (_79_1354) with
| (x, _79_1353) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _79_1363 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _79_1363.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _79_1363.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _79_1369; FStar_Extraction_ML_Syntax.loc = _79_1367})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _79_1376 = head
in {FStar_Extraction_ML_Syntax.expr = _79_1376.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _79_1376.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _79_1379 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_79_1384) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _174_422 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_174_422), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _79_1387 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _79_1389 -> begin
(

let _79_1393 = (term_as_mlexpr g head)
in (match (_79_1393) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head ((f), (t)) args)
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(

let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (

let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let _79_1410 = (check_term_as_mlexpr g e0 f t)
in (match (_79_1410) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _79_1426 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (e'))
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _174_423 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _174_423))
in (

let lb = (

let _79_1420 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _79_1420.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _79_1420.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _79_1420.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _79_1420.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end
end
in (match (_79_1426) with
| (lbs, e') -> begin
(

let lbs = if top_level then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let tcenv = (let _174_425 = (FStar_Ident.lid_of_path (FStar_List.append (Prims.fst g.FStar_Extraction_ML_UEnv.currentModule) (((Prims.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv _174_425))
in (

let lbdef = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
in (

let _79_1430 = lb
in {FStar_Syntax_Syntax.lbname = _79_1430.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _79_1430.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _79_1430.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _79_1430.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))))
end else begin
lbs
end
in (

let maybe_generalize = (fun _79_1440 -> (match (_79_1440) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _79_1438; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _174_428 = (FStar_List.hd bs)
in (FStar_All.pipe_right _174_428 (is_type_binder g))) -> begin
(

let _79_1449 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_1449) with
| (bs, c) -> begin
(

let _79_1459 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _174_430 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_174_430)))
end)
in (match (_79_1459) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_1465) -> begin
(

let _79_1470 = (FStar_Syntax_Subst.open_term bs body)
in (match (_79_1470) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _79_1473 = (FStar_Util.first_N n_tbinders bs)
in (match (_79_1473) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _79_1477 _79_1481 -> (match (((_79_1477), (_79_1481))) with
| ((x, _79_1476), (y, _79_1480)) -> begin
(let _174_434 = (let _174_433 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_174_433)))
in FStar_Syntax_Syntax.NT (_174_434))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _79_1488 -> (match (_79_1488) with
| (a, _79_1487) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _174_438 = (FStar_All.pipe_right targs (FStar_List.map (fun _79_1494 -> (match (_79_1494) with
| (x, _79_1493) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_174_438), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _79_1498 -> begin
false
end)
in (

let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| _79_1503 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in ((lbname_), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env _79_1518 -> (match (_79_1518) with
| (a, _79_1517) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _174_442 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _79_1524 -> (match (_79_1524) with
| (x, _79_1523) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_174_442), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _79_1529 -> (match (_79_1529) with
| (bv, _79_1528) -> begin
(let _174_444 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _174_444 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args)))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| _79_1533 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _79_1535 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _79_1550 -> (match (_79_1550) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _79_1555 -> (match (_79_1555) with
| (a, _79_1554) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let _79_1561 = (check_term_as_mlexpr env e f expected_t)
in (match (_79_1561) with
| (e, _79_1560) -> begin
(

let f = (maybe_downgrade_eff env f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _79_1586 = (FStar_List.fold_right (fun lb _79_1567 -> (match (_79_1567) with
| (env, lbs) -> begin
(

let _79_1580 = lb
in (match (_79_1580) with
| (lbname, _79_1570, (t, (_79_1573, polytype)), add_unit, _79_1579) -> begin
(

let _79_1583 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_79_1583) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_79_1586) with
| (env_body, lbs) -> begin
(

let env_def = if is_rec then begin
env_body
end else begin
g
end
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'.FStar_Syntax_Syntax.pos
in (

let _79_1593 = (term_as_mlexpr env_body e')
in (match (_79_1593) with
| (e', f', t') -> begin
(

let f = (let _174_454 = (let _174_453 = (FStar_List.map Prims.fst lbs)
in (f')::_174_453)
in (FStar_Extraction_ML_Util.join_l e'_rng _174_454))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NonRec
end
in (let _174_459 = (let _174_458 = (let _174_456 = (let _174_455 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_174_455)))
in (mk_MLE_Let top_level _174_456 e'))
in (let _174_457 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _174_458 _174_457)))
in ((_174_459), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _79_1603 = (term_as_mlexpr g scrutinee)
in (match (_79_1603) with
| (e, f_e, t_e) -> begin
(

let _79_1607 = (check_pats_for_ite pats)
in (match (_79_1607) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _79_1619 = (term_as_mlexpr g then_e)
in (match (_79_1619) with
| (then_mle, f_then, t_then) -> begin
(

let _79_1623 = (term_as_mlexpr g else_e)
in (match (_79_1623) with
| (else_mle, f_else, t_else) -> begin
(

let _79_1626 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_79_1626) with
| (t_branch, maybe_lift) -> begin
(let _174_490 = (let _174_488 = (let _174_487 = (let _174_486 = (maybe_lift then_mle t_then)
in (let _174_485 = (let _174_484 = (maybe_lift else_mle t_else)
in Some (_174_484))
in ((e), (_174_486), (_174_485))))
in FStar_Extraction_ML_Syntax.MLE_If (_174_487))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _174_488))
in (let _174_489 = (FStar_Extraction_ML_Util.join then_e.FStar_Syntax_Syntax.pos f_then f_else)
in ((_174_490), (_174_489), (t_branch))))
end))
end))
end))
end
| _79_1628 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _79_1660 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _79_1634 = (FStar_Syntax_Subst.open_branch br)
in (match (_79_1634) with
| (pat, when_opt, branch) -> begin
(

let _79_1638 = (extract_pat g pat t_e)
in (match (_79_1638) with
| (env, p, pat_t_compat) -> begin
(

let _79_1649 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _79_1645 = (term_as_mlexpr env w)
in (match (_79_1645) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_79_1649) with
| (when_opt, f_when) -> begin
(

let _79_1653 = (term_as_mlexpr env branch)
in (match (_79_1653) with
| (mlbranch, f_branch, t_branch) -> begin
(let _174_494 = (FStar_All.pipe_right p (FStar_List.map (fun _79_1656 -> (match (_79_1656) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_174_494)))
end))
end))
end))
end))) true))
in (match (_79_1660) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = if pat_t_compat then begin
e
end else begin
(

let _79_1664 = (FStar_Extraction_ML_UEnv.debug g (fun _79_1662 -> (let _174_497 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _174_496 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" _174_497 _174_496)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
in (match (mlbranches) with
| [] -> begin
(

let _79_1673 = (let _174_499 = (let _174_498 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _174_498))
in (FStar_All.pipe_left FStar_Util.right _174_499))
in (match (_79_1673) with
| (fw, _79_1670, _79_1672) -> begin
(let _174_504 = (let _174_503 = (let _174_502 = (let _174_501 = (let _174_500 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_174_500)::[])
in ((fw), (_174_501)))
in FStar_Extraction_ML_Syntax.MLE_App (_174_502))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _174_503))
in ((_174_504), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_79_1676, _79_1678, (_79_1680, f_first, t_first)))::rest -> begin
(

let _79_1706 = (FStar_List.fold_left (fun _79_1688 _79_1698 -> (match (((_79_1688), (_79_1698))) with
| ((topt, f), (_79_1690, _79_1692, (_79_1694, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
if (type_leq g t t_branch) then begin
Some (t_branch)
end else begin
if (type_leq g t_branch t) then begin
Some (t)
end else begin
None
end
end
end)
in ((topt), (f))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (_79_1706) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _79_1717 -> (match (_79_1717) with
| (p, (wopt, _79_1710), (b, _79_1714, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_79_1720) -> begin
b
end)
in ((p), (wopt), (b)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _174_508 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_174_508), (f_match), (t_match)))))
end))
end)))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> (

let _79_1730 = (FStar_Util.incr c)
in (let _174_511 = (FStar_ST.read c)
in ((x), (_174_511))))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _79_1738 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_79_1738) with
| (_79_1736, fstar_disc_type) -> begin
(

let wildcards = (match ((let _174_518 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _174_518.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _79_1741) -> begin
(let _174_522 = (FStar_All.pipe_right binders (FStar_List.filter (fun _79_6 -> (match (_79_6) with
| (_79_1746, Some (FStar_Syntax_Syntax.Implicit (_79_1748))) -> begin
true
end
| _79_1753 -> begin
false
end))))
in (FStar_All.pipe_right _174_522 (FStar_List.map (fun _79_1754 -> (let _174_521 = (fresh "_")
in ((_174_521), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _79_1757 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _174_537 = (let _174_536 = (let _174_535 = (let _174_534 = (let _174_533 = (let _174_532 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _174_531 = (let _174_530 = (let _174_526 = (let _174_524 = (let _174_523 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_174_523), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_174_524))
in (let _174_525 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_174_526), (None), (_174_525))))
in (let _174_529 = (let _174_528 = (let _174_527 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_174_527)))
in (_174_528)::[])
in (_174_530)::_174_529))
in ((_174_532), (_174_531))))
in FStar_Extraction_ML_Syntax.MLE_Match (_174_533))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _174_534))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_174_535)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_174_536))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _174_537))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




