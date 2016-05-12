
open Prims
# 36 "FStar.Extraction.ML.Term.fst"
exception Un_extractable

# 36 "FStar.Extraction.ML.Term.fst"
let is_Un_extractable = (fun _discr_ -> (match (_discr_) with
| Un_extractable (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Extraction.ML.Term.fst"
let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))

# 51 "FStar.Extraction.ML.Term.fst"
let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))

# 52 "FStar.Extraction.ML.Term.fst"
let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))

# 53 "FStar.Extraction.ML.Term.fst"
let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))

# 60 "FStar.Extraction.ML.Term.fst"
let fail = (fun r msg -> (
# 61 "FStar.Extraction.ML.Term.fst"
let _77_17 = (let _166_29 = (let _166_28 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _166_28 msg))
in (FStar_All.pipe_left FStar_Util.print_string _166_29))
in (FStar_All.failwith msg)))

# 64 "FStar.Extraction.ML.Term.fst"
let err_uninst = (fun env t _77_23 -> (match (_77_23) with
| (vars, ty) -> begin
(let _166_37 = (let _166_36 = (FStar_Syntax_Print.term_to_string t)
in (let _166_35 = (let _166_33 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _166_33 (FStar_String.concat ", ")))
in (let _166_34 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _166_36 _166_35 _166_34))))
in (fail t.FStar_Syntax_Syntax.pos _166_37))
end))

# 70 "FStar.Extraction.ML.Term.fst"
let err_ill_typed_application = (fun t args ty -> (let _166_45 = (let _166_44 = (FStar_Syntax_Print.term_to_string t)
in (let _166_43 = (let _166_42 = (FStar_All.pipe_right args (FStar_List.map (fun _77_30 -> (match (_77_30) with
| (x, _77_29) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _166_42 (FStar_String.concat " ")))
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _166_44 _166_43)))
in (fail t.FStar_Syntax_Syntax.pos _166_45)))

# 76 "FStar.Extraction.ML.Term.fst"
let err_value_restriction = (fun t -> (fail t.FStar_Syntax_Syntax.pos "Refusing to generalize because of the value restriction"))

# 79 "FStar.Extraction.ML.Term.fst"
let err_unexpected_eff = (fun t f0 f1 -> (let _166_51 = (let _166_50 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _166_50 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _166_51)))

# 85 "FStar.Extraction.ML.Term.fst"
let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (
# 86 "FStar.Extraction.ML.Term.fst"
let cache = (FStar_Util.smap_create 20)
in (
# 87 "FStar.Extraction.ML.Term.fst"
let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(
# 91 "FStar.Extraction.ML.Term.fst"
let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv FStar_Syntax_Syntax.U_zero l)) with
| None -> begin
l
end
| Some (_77_44, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (
# 94 "FStar.Extraction.ML.Term.fst"
let _77_49 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in (fun g l -> (
# 97 "FStar.Extraction.ML.Term.fst"
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

# 108 "FStar.Extraction.ML.Term.fst"
type level_t =
| Term_level
| Type_level
| Kind_level

# 109 "FStar.Extraction.ML.Term.fst"
let is_Term_level = (fun _discr_ -> (match (_discr_) with
| Term_level (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.Extraction.ML.Term.fst"
let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Extraction.ML.Term.fst"
let is_Kind_level = (fun _discr_ -> (match (_discr_) with
| Kind_level (_) -> begin
true
end
| _ -> begin
false
end))

# 113 "FStar.Extraction.ML.Term.fst"
let predecessor = (fun t _77_1 -> (match (_77_1) with
| Term_level -> begin
Term_level
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))

# 121 "FStar.Extraction.ML.Term.fst"
let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (
# 122 "FStar.Extraction.ML.Term.fst"
let predecessor = (fun l -> (predecessor t l))
in (
# 123 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_77_65) -> begin
(let _166_75 = (let _166_74 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _166_74))
in (FStar_All.failwith _166_75))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_77_69) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _77_77; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_77_74); FStar_Syntax_Syntax.fv_qual = _77_72}) -> begin
(
# 137 "FStar.Extraction.ML.Term.fst"
let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (
# 138 "FStar.Extraction.ML.Term.fst"
let _77_82 = (FStar_Extraction_ML_UEnv.debug env (fun _77_81 -> (match (()) with
| () -> begin
(let _166_78 = (FStar_Syntax_Print.term_to_string t)
in (let _166_77 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _166_78 _166_77)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _166_79 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _166_79))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _166_80 = (level env t)
in (FStar_All.pipe_left predecessor _166_80))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _77_105, _77_107) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_77_111) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _77_115) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _77_120) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_134) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_77_138, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_77_143, branches) -> begin
(match (branches) with
| (_77_150, _77_152, e)::_77_148 -> begin
(level env e)
end
| _77_157 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _77_160) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _77_165) -> begin
(level env head)
end))))

# 192 "FStar.Extraction.ML.Term.fst"
let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _77_172 -> begin
true
end))

# 196 "FStar.Extraction.ML.Term.fst"
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

# 202 "FStar.Extraction.ML.Term.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _166_89 = (FStar_Syntax_Subst.compress t)
in _166_89.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _77_198 -> begin
false
end))

# 209 "FStar.Extraction.ML.Term.fst"
let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _166_92 = (FStar_Syntax_Subst.compress t)
in _166_92.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _77_219 -> (match (_77_219) with
| (te, _77_218) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _77_232 -> begin
false
end))

# 234 "FStar.Extraction.ML.Term.fst"
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_77_253, fields) -> begin
(FStar_Util.for_all (fun _77_260 -> (match (_77_260) with
| (_77_258, e) -> begin
(is_ml_value e)
end)) fields)
end
| _77_262 -> begin
false
end))

# 247 "FStar.Extraction.ML.Term.fst"
let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (
# 248 "FStar.Extraction.ML.Term.fst"
let rec aux = (fun bs t copt -> (
# 249 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _77_275 -> begin
(
# 253 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))

# 259 "FStar.Extraction.ML.Term.fst"
let unit_binder : FStar_Syntax_Syntax.binder = (let _166_105 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _166_105))

# 263 "FStar.Extraction.ML.Term.fst"
let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (
# 266 "FStar.Extraction.ML.Term.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 269 "FStar.Extraction.ML.Term.fst"
let _77_282 = (FStar_List.hd l)
in (match (_77_282) with
| (p1, w1, e1) -> begin
(
# 270 "FStar.Extraction.ML.Term.fst"
let _77_286 = (let _166_108 = (FStar_List.tl l)
in (FStar_List.hd _166_108))
in (match (_77_286) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _77_306 -> begin
def
end)
end))
end))
end))

# 300 "FStar.Extraction.ML.Term.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 305 "FStar.Extraction.ML.Term.fst"
let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))

# 310 "FStar.Extraction.ML.Term.fst"
let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (
# 311 "FStar.Extraction.ML.Term.fst"
let e = if (erasable g f ty) then begin
if (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, ty))))
end
end else begin
e
end
in (e, f, ty)))

# 319 "FStar.Extraction.ML.Term.fst"
let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (
# 320 "FStar.Extraction.ML.Term.fst"
let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _77_327 -> begin
(
# 324 "FStar.Extraction.ML.Term.fst"
let _77_329 = (FStar_Extraction_ML_UEnv.debug g (fun _77_328 -> (match (()) with
| () -> begin
(let _166_138 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _166_137 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _166_136 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _166_138 _166_137 _166_136))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))

# 333 "FStar.Extraction.ML.Term.fst"
let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_77_334, t) -> begin
t
end
| _77_339 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

# 352 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (
# 353 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (
# 357 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _166_159 = (let _166_158 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _166_158))
in (FStar_All.failwith _166_159))
end
| FStar_Syntax_Syntax.Tm_uvar (_77_357) -> begin
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
# 380 "FStar.Extraction.ML.Term.fst"
let _77_393 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_393) with
| (bs, c) -> begin
(
# 381 "FStar.Extraction.ML.Term.fst"
let _77_396 = (binders_as_ml_binders env bs)
in (match (_77_396) with
| (mlbs, env) -> begin
(
# 382 "FStar.Extraction.ML.Term.fst"
let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (
# 383 "FStar.Extraction.ML.Term.fst"
let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (
# 384 "FStar.Extraction.ML.Term.fst"
let _77_409 = (FStar_List.fold_right (fun _77_402 _77_405 -> (match ((_77_402, _77_405)) with
| ((_77_400, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_77_409) with
| (_77_407, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 390 "FStar.Extraction.ML.Term.fst"
let res = (match ((let _166_162 = (FStar_Syntax_Subst.compress head)
in _166_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _166_163 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _166_163))
end
| _77_423 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _77_428) -> begin
(
# 406 "FStar.Extraction.ML.Term.fst"
let _77_433 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_77_433) with
| (bs, ty) -> begin
(
# 407 "FStar.Extraction.ML.Term.fst"
let _77_436 = (binders_as_ml_binders env bs)
in (match (_77_436) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _77_450 -> (match (_77_450) with
| (a, _77_449) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (
# 420 "FStar.Extraction.ML.Term.fst"
let _77_456 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_77_456) with
| (formals, t) -> begin
(
# 421 "FStar.Extraction.ML.Term.fst"
let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (
# 422 "FStar.Extraction.ML.Term.fst"
let mlargs = (
# 423 "FStar.Extraction.ML.Term.fst"
let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(
# 425 "FStar.Extraction.ML.Term.fst"
let _77_462 = (FStar_Util.first_N n_args formals)
in (match (_77_462) with
| (_77_460, rest) -> begin
(let _166_170 = (FStar_List.map (fun _77_463 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _166_170))
end))
end else begin
mlargs
end)
in (let _166_172 = (let _166_171 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _166_171))
in FStar_Extraction_ML_Syntax.MLTY_Named (_166_172))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (
# 431 "FStar.Extraction.ML.Term.fst"
let _77_481 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _77_470 b -> (match (_77_470) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(
# 434 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 435 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 436 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _166_177 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_166_177, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(
# 439 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 440 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (
# 441 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (
# 442 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _166_178 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_166_178, t))
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_77_481) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))

# 455 "FStar.Extraction.ML.Term.fst"
let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match ((e1.FStar_Extraction_ML_Syntax.expr, e2.FStar_Extraction_ML_Syntax.expr)) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _77_492) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_77_495, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _77_500 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))

# 468 "FStar.Extraction.ML.Term.fst"
let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (false, lb::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _77_515 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _77_517 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _77_519 -> begin
FStar_Extraction_ML_Syntax.MLE_Let ((lbs, body))
end)
end
| _77_521 -> begin
FStar_Extraction_ML_Syntax.MLE_Let ((lbs, body))
end))

# 482 "FStar.Extraction.ML.Term.fst"
let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _77_531 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_77_533, fns)) -> begin
(
# 489 "FStar.Extraction.ML.Term.fst"
let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (
# 490 "FStar.Extraction.ML.Term.fst"
let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _77_541 -> begin
p
end)
end)
end
| _77_543 -> begin
p
end))

# 500 "FStar.Extraction.ML.Term.fst"
let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (
# 501 "FStar.Extraction.ML.Term.fst"
let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (
# 502 "FStar.Extraction.ML.Term.fst"
let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(type_leq g t t')
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_77_559) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 512 "FStar.Extraction.ML.Term.fst"
let i = FStar_Const.Const_int ((c, None))
in (
# 514 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (
# 515 "FStar.Extraction.ML.Term.fst"
let when_clause = (let _166_219 = (let _166_218 = (let _166_217 = (let _166_216 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _166_215 = (let _166_214 = (let _166_213 = (let _166_212 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _166_211 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_211)) _166_212))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _166_213))
in (_166_214)::[])
in (_166_216)::_166_215))
in (FStar_Extraction_ML_Util.prims_op_equality, _166_217))
in FStar_Extraction_ML_Syntax.MLE_App (_166_218))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_219))
in (let _166_220 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])), _166_220)))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(
# 521 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Tc.tc_constant FStar_Range.dummyRange s)
in (
# 522 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g t)
in (let _166_225 = (let _166_223 = (let _166_222 = (let _166_221 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_166_221))
in (_166_222, []))
in Some (_166_223))
in (let _166_224 = (ok mlty)
in (g, _166_225, _166_224)))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 526 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 527 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _166_230 = if imp then begin
None
end else begin
(let _166_228 = (let _166_227 = (let _166_226 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_166_226))
in (_166_227, []))
in Some (_166_228))
end
in (let _166_229 = (ok mlty)
in (g, _166_230, _166_229)))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 534 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 535 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _166_235 = if imp then begin
None
end else begin
(let _166_233 = (let _166_232 = (let _166_231 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_166_231))
in (_166_232, []))
in Some (_166_233))
end
in (let _166_234 = (ok mlty)
in (g, _166_235, _166_234)))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_77_584) -> begin
(g, None, true)
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(
# 542 "FStar.Extraction.ML.Term.fst"
let _77_606 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _77_593; FStar_Extraction_ML_Syntax.loc = _77_591}, ttys, _77_599) -> begin
(n, ttys)
end
| _77_603 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_77_606) with
| (d, tys) -> begin
(
# 545 "FStar.Extraction.ML.Term.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 546 "FStar.Extraction.ML.Term.fst"
let _77_610 = (FStar_Util.first_N nTyVars pats)
in (match (_77_610) with
| (tysVarPats, restPats) -> begin
(
# 547 "FStar.Extraction.ML.Term.fst"
let pat_ty_compat = (match (expected_topt) with
| None -> begin
true
end
| Some (expected_t) -> begin
try
(match (()) with
| () -> begin
(
# 552 "FStar.Extraction.ML.Term.fst"
let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _77_623 -> (match (_77_623) with
| (p, _77_622) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_77_625, t) -> begin
(term_as_mlty g t)
end
| _77_630 -> begin
(Prims.raise Un_extractable)
end)
end))))
in (
# 556 "FStar.Extraction.ML.Term.fst"
let pat_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (type_leq g pat_ty expected_t)))
end)
with
| Un_extractable -> begin
false
end
end)
in (
# 559 "FStar.Extraction.ML.Term.fst"
let _77_645 = (FStar_Util.fold_map (fun g _77_637 -> (match (_77_637) with
| (p, imp) -> begin
(
# 560 "FStar.Extraction.ML.Term.fst"
let _77_642 = (extract_one_pat disjunctive_pat true g p None)
in (match (_77_642) with
| (g, p, _77_641) -> begin
(g, p)
end))
end)) g tysVarPats)
in (match (_77_645) with
| (g, tyMLPats) -> begin
(
# 562 "FStar.Extraction.ML.Term.fst"
let _77_657 = (FStar_Util.fold_map (fun g _77_649 -> (match (_77_649) with
| (p, imp) -> begin
(
# 563 "FStar.Extraction.ML.Term.fst"
let _77_654 = (extract_one_pat disjunctive_pat false g p None)
in (match (_77_654) with
| (g, p, _77_653) -> begin
(g, p)
end))
end)) g restPats)
in (match (_77_657) with
| (g, restMLPats) -> begin
(
# 565 "FStar.Extraction.ML.Term.fst"
let _77_665 = (let _166_244 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _77_2 -> (match (_77_2) with
| Some (x) -> begin
(x)::[]
end
| _77_662 -> begin
[]
end))))
in (FStar_All.pipe_right _166_244 FStar_List.split))
in (match (_77_665) with
| (mlPats, when_clauses) -> begin
(let _166_248 = (let _166_247 = (let _166_246 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _166_245 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_166_246, _166_245)))
in Some (_166_247))
in (g, _166_248, pat_ty_compat))
end))
end))
end)))
end)))
end))
end)))
in (
# 569 "FStar.Extraction.ML.Term.fst"
let extract_one_pat = (fun disj g p expected_t -> (match ((extract_one_pat disj false g p expected_t)) with
| (g, Some (x, v), b) -> begin
(g, (x, v), b)
end
| _77_679 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (
# 574 "FStar.Extraction.ML.Term.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _166_259 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_166_259))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(
# 583 "FStar.Extraction.ML.Term.fst"
let _77_695 = (extract_one_pat true g p (Some (expected_t)))
in (match (_77_695) with
| (g, p, b) -> begin
(
# 584 "FStar.Extraction.ML.Term.fst"
let _77_705 = (FStar_Util.fold_map (fun b p -> (
# 585 "FStar.Extraction.ML.Term.fst"
let _77_702 = (extract_one_pat true g p (Some (expected_t)))
in (match (_77_702) with
| (_77_699, p, b') -> begin
((b && b'), p)
end))) b pats)
in (match (_77_705) with
| (b, ps) -> begin
(
# 587 "FStar.Extraction.ML.Term.fst"
let ps = (p)::ps
in (
# 588 "FStar.Extraction.ML.Term.fst"
let _77_720 = (FStar_All.pipe_right ps (FStar_List.partition (fun _77_3 -> (match (_77_3) with
| (_77_709, _77_713::_77_711) -> begin
true
end
| _77_717 -> begin
false
end))))
in (match (_77_720) with
| (ps_when, rest) -> begin
(
# 589 "FStar.Extraction.ML.Term.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _77_723 -> (match (_77_723) with
| (x, whens) -> begin
(let _166_264 = (mk_when_clause whens)
in (x, _166_264))
end))))
in (
# 591 "FStar.Extraction.ML.Term.fst"
let res = (match (rest) with
| [] -> begin
(g, ps, b)
end
| rest -> begin
(let _166_268 = (let _166_267 = (let _166_266 = (let _166_265 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_166_265))
in (_166_266, None))
in (_166_267)::ps)
in (g, _166_268, b))
end)
in res))
end)))
end))
end))
end
| _77_729 -> begin
(
# 597 "FStar.Extraction.ML.Term.fst"
let _77_735 = (extract_one_pat false g p (Some (expected_t)))
in (match (_77_735) with
| (g, (p, whens), b) -> begin
(
# 598 "FStar.Extraction.ML.Term.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[], b))
end))
end)))))

# 617 "FStar.Extraction.ML.Term.fst"
let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 618 "FStar.Extraction.ML.Term.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _77_746, t1) -> begin
(
# 620 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _166_283 = (let _166_282 = (let _166_281 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _166_281))
in (_166_282)::more_args)
in (eta_args _166_283 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_77_752, _77_754) -> begin
((FStar_List.rev more_args), t)
end
| _77_758 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (
# 625 "FStar.Extraction.ML.Term.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_77_763, args), Some (FStar_Syntax_Syntax.Record_ctor (_77_768, fields))) -> begin
(
# 628 "FStar.Extraction.ML.Term.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 629 "FStar.Extraction.ML.Term.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _77_777 -> begin
e
end))
in (
# 633 "FStar.Extraction.ML.Term.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 634 "FStar.Extraction.ML.Term.fst"
let _77_783 = (eta_args [] residualType)
in (match (_77_783) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _166_292 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _166_292))
end
| _77_786 -> begin
(
# 638 "FStar.Extraction.ML.Term.fst"
let _77_789 = (FStar_List.unzip eargs)
in (match (_77_789) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 641 "FStar.Extraction.ML.Term.fst"
let body = (let _166_294 = (let _166_293 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _166_293))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _166_294))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _77_796 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_77_798, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _77_804; FStar_Extraction_ML_Syntax.loc = _77_802}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(
# 649 "FStar.Extraction.ML.Term.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 650 "FStar.Extraction.ML.Term.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 651 "FStar.Extraction.ML.Term.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _77_821 -> begin
(let _166_296 = (let _166_295 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_166_295, args))
in FStar_Extraction_ML_Syntax.MLE_App (_166_296))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _166_297 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_297))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _166_298 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_298))
end
| _77_861 -> begin
mlAppExpr
end)))))

# 667 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (
# 668 "FStar.Extraction.ML.Term.fst"
let _77_867 = (term_as_mlexpr' g t)
in (match (_77_867) with
| (e, tag, ty) -> begin
(
# 669 "FStar.Extraction.ML.Term.fst"
let _77_869 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _166_317 = (let _166_316 = (FStar_Syntax_Print.tag_of_term t)
in (let _166_315 = (FStar_Syntax_Print.term_to_string t)
in (let _166_314 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "term_as_mlexpr (%s) :  %s has ML type %s\n" _166_316 _166_315 _166_314))))
in (FStar_Util.print_string _166_317))))
in (erase g e ty tag))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (
# 677 "FStar.Extraction.ML.Term.fst"
let _77_877 = (check_term_as_mlexpr' g t f ty)
in (match (_77_877) with
| (e, t) -> begin
(
# 678 "FStar.Extraction.ML.Term.fst"
let _77_882 = (erase g e t f)
in (match (_77_882) with
| (r, _77_880, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (
# 682 "FStar.Extraction.ML.Term.fst"
let _77_890 = (term_as_mlexpr g e0)
in (match (_77_890) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _166_326 = (maybe_coerce g e t ty)
in (_166_326, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (
# 688 "FStar.Extraction.ML.Term.fst"
let _77_894 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _166_332 = (let _166_331 = (FStar_Syntax_Print.tag_of_term top)
in (let _166_330 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _166_331 _166_330)))
in (FStar_Util.print_string _166_332))))
in (
# 689 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _166_334 = (let _166_333 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _166_333))
in (FStar_All.failwith _166_334))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 706 "FStar.Extraction.ML.Term.fst"
let _77_932 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_77_932) with
| (_77_928, ty, _77_931) -> begin
(
# 707 "FStar.Extraction.ML.Term.fst"
let ml_ty = (term_as_mlty g ty)
in (let _166_338 = (let _166_337 = (let _166_336 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _166_335 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_335)) _166_336))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _166_337))
in (_166_338, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_77_941), _77_944) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _77_949), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, t)
end
| ([], t) -> begin
(let _166_339 = (maybe_eta_data_and_project_record g qual t x)
in (_166_339, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _77_961 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(
# 728 "FStar.Extraction.ML.Term.fst"
let _77_969 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_969) with
| (bs, body) -> begin
(
# 729 "FStar.Extraction.ML.Term.fst"
let _77_972 = (binders_as_ml_binders g bs)
in (match (_77_972) with
| (ml_bs, env) -> begin
(
# 730 "FStar.Extraction.ML.Term.fst"
let _77_976 = (term_as_mlexpr env body)
in (match (_77_976) with
| (ml_body, f, t) -> begin
(
# 731 "FStar.Extraction.ML.Term.fst"
let _77_986 = (FStar_List.fold_right (fun _77_980 _77_983 -> (match ((_77_980, _77_983)) with
| ((_77_978, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_77_986) with
| (f, tfun) -> begin
(let _166_342 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_166_342, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_77_992) -> begin
(
# 739 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _77_996 -> begin
(
# 742 "FStar.Extraction.ML.Term.fst"
let rec extract_app = (fun is_data _77_1001 _77_1004 restArgs -> (match ((_77_1001, _77_1004)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _77_1008) -> begin
(
# 750 "FStar.Extraction.ML.Term.fst"
let _77_1019 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _166_351 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _166_351))
end else begin
(FStar_List.fold_left (fun _77_1012 _77_1015 -> (match ((_77_1012, _77_1015)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 756 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _166_355 = (let _166_354 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_166_354)::out_args)
in (((x, arg))::lbs, _166_355)))
end
end)) ([], []) mlargs_f)
end
in (match (_77_1019) with
| (lbs, mlargs) -> begin
(
# 759 "FStar.Extraction.ML.Term.fst"
let app = (let _166_356 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _166_356))
in (
# 760 "FStar.Extraction.ML.Term.fst"
let l_app = (FStar_List.fold_right (fun _77_1023 out -> (match (_77_1023) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false (false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]) out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _77_1029)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _166_360 = (let _166_359 = (FStar_Extraction_ML_Util.join f f')
in (_166_359, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _166_360 rest))
end else begin
(let _166_365 = (let _166_364 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _166_363 = (FStar_Syntax_Print.term_to_string arg)
in (let _166_362 = (FStar_Syntax_Print.tag_of_term arg)
in (let _166_361 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _166_364 _166_363 _166_362 _166_361)))))
in (FStar_All.failwith _166_365))
end
end
| ((e0, _77_1041)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 776 "FStar.Extraction.ML.Term.fst"
let _77_1053 = (term_as_mlexpr g e0)
in (match (_77_1053) with
| (e0, f0, tInferred) -> begin
(
# 777 "FStar.Extraction.ML.Term.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _166_367 = (let _166_366 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_166_366, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _166_367 rest)))
end))
end
| _77_1056 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application top restArgs t)
end)
end)
end))
in (
# 786 "FStar.Extraction.ML.Term.fst"
let extract_app_maybe_projector = (fun is_data mlhead _77_1065 args -> (match (_77_1065) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_77_1068)) -> begin
(
# 789 "FStar.Extraction.ML.Term.fst"
let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((_77_1077, Some (FStar_Syntax_Syntax.Implicit (_77_1079)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_77_1085, f', t)) -> begin
(let _166_382 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _166_382 t))
end
| _77_1092 -> begin
(args, f, t)
end))
in (
# 794 "FStar.Extraction.ML.Term.fst"
let _77_1096 = (remove_implicits args f t)
in (match (_77_1096) with
| (args, f, t) -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)))
end
| _77_1098 -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)
end))
in if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(
# 802 "FStar.Extraction.ML.Term.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 807 "FStar.Extraction.ML.Term.fst"
let _77_1119 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _77_1111 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_77_1119) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 808 "FStar.Extraction.ML.Term.fst"
let has_typ_apps = (match (args) with
| (a, _77_1124)::_77_1121 -> begin
(is_type g a)
end
| _77_1128 -> begin
false
end)
in (
# 812 "FStar.Extraction.ML.Term.fst"
let _77_1174 = (match (vars) with
| _77_1133::_77_1131 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _77_1136 -> begin
(
# 819 "FStar.Extraction.ML.Term.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 821 "FStar.Extraction.ML.Term.fst"
let _77_1140 = (FStar_Util.first_N n args)
in (match (_77_1140) with
| (prefix, rest) -> begin
(
# 823 "FStar.Extraction.ML.Term.fst"
let prefixAsMLTypes = (FStar_List.map (fun _77_1144 -> (match (_77_1144) with
| (x, _77_1143) -> begin
(term_as_mlty g x)
end)) prefix)
in (
# 825 "FStar.Extraction.ML.Term.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 826 "FStar.Extraction.ML.Term.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 828 "FStar.Extraction.ML.Term.fst"
let _77_1153 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _77_1153.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _77_1153.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _77_1159; FStar_Extraction_ML_Syntax.loc = _77_1157}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 829 "FStar.Extraction.ML.Term.fst"
let _77_1166 = head
in {FStar_Extraction_ML_Syntax.expr = _77_1166.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _77_1166.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _77_1169 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_77_1174) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _166_384 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_166_384, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _77_1177 -> begin
(extract_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _77_1179 -> begin
(
# 840 "FStar.Extraction.ML.Term.fst"
let _77_1183 = (term_as_mlexpr g head)
in (match (_77_1183) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head (f, t) args)
end))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(
# 846 "FStar.Extraction.ML.Term.fst"
let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (
# 849 "FStar.Extraction.ML.Term.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (
# 852 "FStar.Extraction.ML.Term.fst"
let _77_1200 = (check_term_as_mlexpr g e0 f t)
in (match (_77_1200) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(
# 856 "FStar.Extraction.ML.Term.fst"
let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (
# 857 "FStar.Extraction.ML.Term.fst"
let _77_1216 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(
# 862 "FStar.Extraction.ML.Term.fst"
let lb = (FStar_List.hd lbs)
in (
# 863 "FStar.Extraction.ML.Term.fst"
let x = (let _166_385 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _166_385))
in (
# 864 "FStar.Extraction.ML.Term.fst"
let lb = (
# 864 "FStar.Extraction.ML.Term.fst"
let _77_1210 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _77_1210.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _77_1210.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _77_1210.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _77_1210.FStar_Syntax_Syntax.lbdef})
in (
# 865 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_77_1216) with
| (lbs, e') -> begin
(
# 868 "FStar.Extraction.ML.Term.fst"
let maybe_generalize = (fun _77_1224 -> (match (_77_1224) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _77_1222; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 869 "FStar.Extraction.ML.Term.fst"
let f_e = (effect_as_etag g lbeff)
in (
# 870 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _166_388 = (FStar_List.hd bs)
in (FStar_All.pipe_right _166_388 (is_type_binder g))) -> begin
(
# 874 "FStar.Extraction.ML.Term.fst"
let _77_1233 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_1233) with
| (bs, c) -> begin
(
# 881 "FStar.Extraction.ML.Term.fst"
let _77_1243 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _166_390 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _166_390))
end)
in (match (_77_1243) with
| (tbinders, tbody) -> begin
(
# 886 "FStar.Extraction.ML.Term.fst"
let n_tbinders = (FStar_List.length tbinders)
in (
# 887 "FStar.Extraction.ML.Term.fst"
let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_1249) -> begin
(
# 890 "FStar.Extraction.ML.Term.fst"
let _77_1254 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_1254) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(
# 892 "FStar.Extraction.ML.Term.fst"
let _77_1257 = (FStar_Util.first_N n_tbinders bs)
in (match (_77_1257) with
| (targs, rest_args) -> begin
(
# 896 "FStar.Extraction.ML.Term.fst"
let expected_t = (
# 897 "FStar.Extraction.ML.Term.fst"
let s = (FStar_List.map2 (fun _77_1261 _77_1265 -> (match ((_77_1261, _77_1265)) with
| ((x, _77_1260), (y, _77_1264)) -> begin
(let _166_394 = (let _166_393 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _166_393))
in FStar_Syntax_Syntax.NT (_166_394))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (
# 900 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _77_1272 -> (match (_77_1272) with
| (a, _77_1271) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (
# 901 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty env expected_t)
in (
# 902 "FStar.Extraction.ML.Term.fst"
let polytype = (let _166_398 = (FStar_All.pipe_right targs (FStar_List.map (fun _77_1278 -> (match (_77_1278) with
| (x, _77_1277) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_166_398, expected_t))
in (
# 903 "FStar.Extraction.ML.Term.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _77_1282 -> begin
false
end)
in (
# 906 "FStar.Extraction.ML.Term.fst"
let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (
# 907 "FStar.Extraction.ML.Term.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _77_1287 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| _77_1290 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _77_1292 -> begin
(
# 938 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 941 "FStar.Extraction.ML.Term.fst"
let check_lb = (fun env _77_1307 -> (match (_77_1307) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 942 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _77_1312 -> (match (_77_1312) with
| (a, _77_1311) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (
# 943 "FStar.Extraction.ML.Term.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 944 "FStar.Extraction.ML.Term.fst"
let _77_1318 = (check_term_as_mlexpr env e f expected_t)
in (match (_77_1318) with
| (e, _77_1317) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (
# 948 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 950 "FStar.Extraction.ML.Term.fst"
let _77_1342 = (FStar_List.fold_right (fun lb _77_1323 -> (match (_77_1323) with
| (env, lbs) -> begin
(
# 951 "FStar.Extraction.ML.Term.fst"
let _77_1336 = lb
in (match (_77_1336) with
| (lbname, _77_1326, (t, (_77_1329, polytype)), add_unit, _77_1335) -> begin
(
# 952 "FStar.Extraction.ML.Term.fst"
let _77_1339 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_77_1339) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_77_1342) with
| (env_body, lbs) -> begin
(
# 955 "FStar.Extraction.ML.Term.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 957 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 959 "FStar.Extraction.ML.Term.fst"
let _77_1348 = (term_as_mlexpr env_body e')
in (match (_77_1348) with
| (e', f', t') -> begin
(
# 961 "FStar.Extraction.ML.Term.fst"
let f = (let _166_408 = (let _166_407 = (FStar_List.map Prims.fst lbs)
in (f')::_166_407)
in (FStar_Extraction_ML_Util.join_l _166_408))
in (let _166_413 = (let _166_412 = (let _166_410 = (let _166_409 = (FStar_List.map Prims.snd lbs)
in (is_rec, _166_409))
in (mk_MLE_Let top_level _166_410 e'))
in (let _166_411 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _166_412 _166_411)))
in (_166_413, f, t')))
end))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(
# 966 "FStar.Extraction.ML.Term.fst"
let _77_1357 = (term_as_mlexpr g scrutinee)
in (match (_77_1357) with
| (e, f_e, t_e) -> begin
(
# 967 "FStar.Extraction.ML.Term.fst"
let _77_1361 = (check_pats_for_ite pats)
in (match (_77_1361) with
| (b, then_e, else_e) -> begin
(
# 968 "FStar.Extraction.ML.Term.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 972 "FStar.Extraction.ML.Term.fst"
let _77_1373 = (term_as_mlexpr g then_e)
in (match (_77_1373) with
| (then_mle, f_then, t_then) -> begin
(
# 973 "FStar.Extraction.ML.Term.fst"
let _77_1377 = (term_as_mlexpr g else_e)
in (match (_77_1377) with
| (else_mle, f_else, t_else) -> begin
(
# 974 "FStar.Extraction.ML.Term.fst"
let _77_1380 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_77_1380) with
| (t_branch, maybe_lift) -> begin
(let _166_444 = (let _166_442 = (let _166_441 = (let _166_440 = (maybe_lift then_mle t_then)
in (let _166_439 = (let _166_438 = (maybe_lift else_mle t_else)
in Some (_166_438))
in (e, _166_440, _166_439)))
in FStar_Extraction_ML_Syntax.MLE_If (_166_441))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _166_442))
in (let _166_443 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_166_444, _166_443, t_branch)))
end))
end))
end))
end
| _77_1382 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 985 "FStar.Extraction.ML.Term.fst"
let _77_1414 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (
# 986 "FStar.Extraction.ML.Term.fst"
let _77_1388 = (FStar_Syntax_Subst.open_branch br)
in (match (_77_1388) with
| (pat, when_opt, branch) -> begin
(
# 987 "FStar.Extraction.ML.Term.fst"
let _77_1392 = (extract_pat g pat t_e)
in (match (_77_1392) with
| (env, p, pat_t_compat) -> begin
(
# 988 "FStar.Extraction.ML.Term.fst"
let _77_1403 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 991 "FStar.Extraction.ML.Term.fst"
let _77_1399 = (term_as_mlexpr env w)
in (match (_77_1399) with
| (w, f_w, t_w) -> begin
(
# 992 "FStar.Extraction.ML.Term.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_77_1403) with
| (when_opt, f_when) -> begin
(
# 994 "FStar.Extraction.ML.Term.fst"
let _77_1407 = (term_as_mlexpr env branch)
in (match (_77_1407) with
| (mlbranch, f_branch, t_branch) -> begin
(let _166_448 = (FStar_All.pipe_right p (FStar_List.map (fun _77_1410 -> (match (_77_1410) with
| (p, wopt) -> begin
(
# 998 "FStar.Extraction.ML.Term.fst"
let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
end))))
in ((compat && pat_t_compat), _166_448))
end))
end))
end))
end))) true))
in (match (_77_1414) with
| (pat_t_compat, mlbranches) -> begin
(
# 1001 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_List.flatten mlbranches)
in (
# 1004 "FStar.Extraction.ML.Term.fst"
let e = if pat_t_compat then begin
e
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t_e, FStar_Extraction_ML_Syntax.MLTY_Top))))
end
in (match (mlbranches) with
| [] -> begin
(
# 1007 "FStar.Extraction.ML.Term.fst"
let _77_1423 = (let _166_450 = (let _166_449 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _166_449))
in (FStar_All.pipe_left FStar_Util.right _166_450))
in (match (_77_1423) with
| (fw, _77_1420, _77_1422) -> begin
(let _166_455 = (let _166_454 = (let _166_453 = (let _166_452 = (let _166_451 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_166_451)::[])
in (fw, _166_452))
in FStar_Extraction_ML_Syntax.MLE_App (_166_453))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _166_454))
in (_166_455, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_77_1426, _77_1428, (_77_1430, f_first, t_first))::rest -> begin
(
# 1014 "FStar.Extraction.ML.Term.fst"
let _77_1456 = (FStar_List.fold_left (fun _77_1438 _77_1448 -> (match ((_77_1438, _77_1448)) with
| ((topt, f), (_77_1440, _77_1442, (_77_1444, f_branch, t_branch))) -> begin
(
# 1018 "FStar.Extraction.ML.Term.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 1019 "FStar.Extraction.ML.Term.fst"
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
in (topt, f)))
end)) (Some (t_first), f_first) rest)
in (match (_77_1456) with
| (topt, f_match) -> begin
(
# 1032 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _77_1467 -> (match (_77_1467) with
| (p, (wopt, _77_1460), (b, _77_1464, t)) -> begin
(
# 1033 "FStar.Extraction.ML.Term.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_77_1470) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 1039 "FStar.Extraction.ML.Term.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _166_459 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_166_459, f_match, t_match))))
end))
end)))
end))
end)
end))
end))
end))))

# 1047 "FStar.Extraction.ML.Term.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 1047 "FStar.Extraction.ML.Term.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 1048 "FStar.Extraction.ML.Term.fst"
let _77_1480 = (FStar_Util.incr c)
in (let _166_462 = (FStar_ST.read c)
in (x, _166_462)))))

# 1050 "FStar.Extraction.ML.Term.fst"
let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 1052 "FStar.Extraction.ML.Term.fst"
let _77_1488 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_77_1488) with
| (_77_1486, fstar_disc_type) -> begin
(
# 1053 "FStar.Extraction.ML.Term.fst"
let wildcards = (match ((let _166_469 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _166_469.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _77_1491) -> begin
(let _166_473 = (FStar_All.pipe_right binders (FStar_List.filter (fun _77_4 -> (match (_77_4) with
| (_77_1496, Some (FStar_Syntax_Syntax.Implicit (_77_1498))) -> begin
true
end
| _77_1503 -> begin
false
end))))
in (FStar_All.pipe_right _166_473 (FStar_List.map (fun _77_1504 -> (let _166_472 = (fresh "_")
in (_166_472, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _77_1507 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 1064 "FStar.Extraction.ML.Term.fst"
let mlid = (fresh "_discr_")
in (
# 1065 "FStar.Extraction.ML.Term.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 1068 "FStar.Extraction.ML.Term.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 1069 "FStar.Extraction.ML.Term.fst"
let discrBody = (let _166_488 = (let _166_487 = (let _166_486 = (let _166_485 = (let _166_484 = (let _166_483 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _166_482 = (let _166_481 = (let _166_477 = (let _166_475 = (let _166_474 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_166_474, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_166_475))
in (let _166_476 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_166_477, None, _166_476)))
in (let _166_480 = (let _166_479 = (let _166_478 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _166_478))
in (_166_479)::[])
in (_166_481)::_166_480))
in (_166_483, _166_482)))
in FStar_Extraction_ML_Syntax.MLE_Match (_166_484))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_485))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _166_486))
in FStar_Extraction_ML_Syntax.MLE_Fun (_166_487))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _166_488))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




