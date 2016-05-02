
open Prims
# 48 "FStar.Extraction.ML.Term.fst"
let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))

# 49 "FStar.Extraction.ML.Term.fst"
let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))

# 50 "FStar.Extraction.ML.Term.fst"
let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))

# 51 "FStar.Extraction.ML.Term.fst"
let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))

# 58 "FStar.Extraction.ML.Term.fst"
let fail = (fun r msg -> (
# 59 "FStar.Extraction.ML.Term.fst"
let _77_17 = (let _166_28 = (let _166_27 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _166_27 msg))
in (FStar_All.pipe_left FStar_Util.print_string _166_28))
in (FStar_All.failwith msg)))

# 62 "FStar.Extraction.ML.Term.fst"
let err_uninst = (fun env t _77_23 -> (match (_77_23) with
| (vars, ty) -> begin
(let _166_36 = (let _166_35 = (FStar_Syntax_Print.term_to_string t)
in (let _166_34 = (let _166_32 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _166_32 (FStar_String.concat ", ")))
in (let _166_33 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _166_35 _166_34 _166_33))))
in (fail t.FStar_Syntax_Syntax.pos _166_36))
end))

# 68 "FStar.Extraction.ML.Term.fst"
let err_ill_typed_application = (fun t args ty -> (let _166_44 = (let _166_43 = (FStar_Syntax_Print.term_to_string t)
in (let _166_42 = (let _166_41 = (FStar_All.pipe_right args (FStar_List.map (fun _77_30 -> (match (_77_30) with
| (x, _77_29) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _166_41 (FStar_String.concat " ")))
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _166_43 _166_42)))
in (fail t.FStar_Syntax_Syntax.pos _166_44)))

# 74 "FStar.Extraction.ML.Term.fst"
let err_value_restriction = (fun t -> (fail t.FStar_Syntax_Syntax.pos "Refusing to generalize because of the value restriction"))

# 77 "FStar.Extraction.ML.Term.fst"
let err_unexpected_eff = (fun t f0 f1 -> (let _166_50 = (let _166_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _166_49 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _166_50)))

# 83 "FStar.Extraction.ML.Term.fst"
let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (
# 84 "FStar.Extraction.ML.Term.fst"
let cache = (FStar_Util.smap_create 20)
in (
# 85 "FStar.Extraction.ML.Term.fst"
let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(
# 89 "FStar.Extraction.ML.Term.fst"
let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv FStar_Syntax_Syntax.U_zero l)) with
| None -> begin
l
end
| Some (_77_44, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (
# 92 "FStar.Extraction.ML.Term.fst"
let _77_49 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in (fun g l -> (
# 95 "FStar.Extraction.ML.Term.fst"
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

# 106 "FStar.Extraction.ML.Term.fst"
type level_t =
| Term_level
| Type_level
| Kind_level

# 107 "FStar.Extraction.ML.Term.fst"
let is_Term_level = (fun _discr_ -> (match (_discr_) with
| Term_level (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.Extraction.ML.Term.fst"
let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.Extraction.ML.Term.fst"
let is_Kind_level = (fun _discr_ -> (match (_discr_) with
| Kind_level (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Extraction.ML.Term.fst"
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

# 119 "FStar.Extraction.ML.Term.fst"
let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (
# 120 "FStar.Extraction.ML.Term.fst"
let predecessor = (fun l -> (predecessor t l))
in (
# 121 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_77_65) -> begin
(let _166_74 = (let _166_73 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _166_73))
in (FStar_All.failwith _166_74))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_77_69) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _77_77; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_77_74); FStar_Syntax_Syntax.fv_qual = _77_72}) -> begin
(
# 135 "FStar.Extraction.ML.Term.fst"
let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (
# 136 "FStar.Extraction.ML.Term.fst"
let _77_82 = (FStar_Extraction_ML_UEnv.debug env (fun _77_81 -> (match (()) with
| () -> begin
(let _166_77 = (FStar_Syntax_Print.term_to_string t)
in (let _166_76 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _166_77 _166_76)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _166_78 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _166_78))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _166_79 = (level env t)
in (FStar_All.pipe_left predecessor _166_79))
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

# 190 "FStar.Extraction.ML.Term.fst"
let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _77_172 -> begin
true
end))

# 194 "FStar.Extraction.ML.Term.fst"
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

# 200 "FStar.Extraction.ML.Term.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _166_88 = (FStar_Syntax_Subst.compress t)
in _166_88.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _77_198 -> begin
false
end))

# 207 "FStar.Extraction.ML.Term.fst"
let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _166_91 = (FStar_Syntax_Subst.compress t)
in _166_91.FStar_Syntax_Syntax.n)) with
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

# 232 "FStar.Extraction.ML.Term.fst"
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

# 245 "FStar.Extraction.ML.Term.fst"
let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (
# 246 "FStar.Extraction.ML.Term.fst"
let rec aux = (fun bs t copt -> (
# 247 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _77_275 -> begin
(
# 251 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))

# 257 "FStar.Extraction.ML.Term.fst"
let unit_binder : FStar_Syntax_Syntax.binder = (let _166_104 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _166_104))

# 261 "FStar.Extraction.ML.Term.fst"
let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (
# 264 "FStar.Extraction.ML.Term.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 267 "FStar.Extraction.ML.Term.fst"
let _77_282 = (FStar_List.hd l)
in (match (_77_282) with
| (p1, w1, e1) -> begin
(
# 268 "FStar.Extraction.ML.Term.fst"
let _77_286 = (let _166_107 = (FStar_List.tl l)
in (FStar_List.hd _166_107))
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

# 298 "FStar.Extraction.ML.Term.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 303 "FStar.Extraction.ML.Term.fst"
let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))

# 308 "FStar.Extraction.ML.Term.fst"
let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (
# 309 "FStar.Extraction.ML.Term.fst"
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

# 317 "FStar.Extraction.ML.Term.fst"
let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (
# 318 "FStar.Extraction.ML.Term.fst"
let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _77_327 -> begin
(
# 322 "FStar.Extraction.ML.Term.fst"
let _77_329 = (FStar_Extraction_ML_UEnv.debug g (fun _77_328 -> (match (()) with
| () -> begin
(let _166_137 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _166_136 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _166_135 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _166_137 _166_136 _166_135))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))

# 331 "FStar.Extraction.ML.Term.fst"
let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_77_334, t) -> begin
t
end
| _77_339 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

# 350 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (
# 351 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (
# 355 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _166_158 = (let _166_157 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _166_157))
in (FStar_All.failwith _166_158))
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
# 378 "FStar.Extraction.ML.Term.fst"
let _77_393 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_393) with
| (bs, c) -> begin
(
# 379 "FStar.Extraction.ML.Term.fst"
let _77_396 = (binders_as_ml_binders env bs)
in (match (_77_396) with
| (mlbs, env) -> begin
(
# 380 "FStar.Extraction.ML.Term.fst"
let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (
# 381 "FStar.Extraction.ML.Term.fst"
let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (
# 382 "FStar.Extraction.ML.Term.fst"
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
# 388 "FStar.Extraction.ML.Term.fst"
let res = (match ((let _166_161 = (FStar_Syntax_Subst.compress head)
in _166_161.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _166_162 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _166_162))
end
| _77_423 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _77_428) -> begin
(
# 404 "FStar.Extraction.ML.Term.fst"
let _77_433 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_77_433) with
| (bs, ty) -> begin
(
# 405 "FStar.Extraction.ML.Term.fst"
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
# 418 "FStar.Extraction.ML.Term.fst"
let _77_456 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_77_456) with
| (formals, t) -> begin
(
# 419 "FStar.Extraction.ML.Term.fst"
let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (
# 420 "FStar.Extraction.ML.Term.fst"
let mlargs = (
# 421 "FStar.Extraction.ML.Term.fst"
let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(
# 423 "FStar.Extraction.ML.Term.fst"
let _77_462 = (FStar_Util.first_N n_args formals)
in (match (_77_462) with
| (_77_460, rest) -> begin
(let _166_169 = (FStar_List.map (fun _77_463 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _166_169))
end))
end else begin
mlargs
end)
in (let _166_171 = (let _166_170 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _166_170))
in FStar_Extraction_ML_Syntax.MLTY_Named (_166_171))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (
# 429 "FStar.Extraction.ML.Term.fst"
let _77_481 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _77_470 b -> (match (_77_470) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(
# 432 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 433 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 434 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _166_176 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_166_176, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(
# 437 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 438 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (
# 439 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (
# 440 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _166_177 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_166_177, t))
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_77_481) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))

# 453 "FStar.Extraction.ML.Term.fst"
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

# 466 "FStar.Extraction.ML.Term.fst"
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

# 480 "FStar.Extraction.ML.Term.fst"
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
# 487 "FStar.Extraction.ML.Term.fst"
let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (
# 488 "FStar.Extraction.ML.Term.fst"
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

# 498 "FStar.Extraction.ML.Term.fst"
let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 499 "FStar.Extraction.ML.Term.fst"
let rec extract_one_pat = (fun disjunctive_pat imp g p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_77_552) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 506 "FStar.Extraction.ML.Term.fst"
let i = FStar_Const.Const_int ((c, None))
in (
# 508 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (
# 509 "FStar.Extraction.ML.Term.fst"
let when_clause = (let _166_212 = (let _166_211 = (let _166_210 = (let _166_209 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _166_208 = (let _166_207 = (let _166_206 = (let _166_205 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _166_204 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_204)) _166_205))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _166_206))
in (_166_207)::[])
in (_166_209)::_166_208))
in (FStar_Extraction_ML_Util.prims_op_equality, _166_210))
in FStar_Extraction_ML_Syntax.MLE_App (_166_211))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_212))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[]))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(let _166_216 = (let _166_215 = (let _166_214 = (let _166_213 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_166_213))
in (_166_214, []))
in Some (_166_215))
in (g, _166_216))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(
# 518 "FStar.Extraction.ML.Term.fst"
let _77_584 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _77_571; FStar_Extraction_ML_Syntax.loc = _77_569}, ttys, _77_577) -> begin
(n, ttys)
end
| _77_581 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_77_584) with
| (d, tys) -> begin
(
# 521 "FStar.Extraction.ML.Term.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 522 "FStar.Extraction.ML.Term.fst"
let _77_588 = (FStar_Util.first_N nTyVars pats)
in (match (_77_588) with
| (tysVarPats, restPats) -> begin
(
# 523 "FStar.Extraction.ML.Term.fst"
let _77_595 = (FStar_Util.fold_map (fun g _77_592 -> (match (_77_592) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat true g p)
end)) g tysVarPats)
in (match (_77_595) with
| (g, tyMLPats) -> begin
(
# 524 "FStar.Extraction.ML.Term.fst"
let _77_602 = (FStar_Util.fold_map (fun g _77_599 -> (match (_77_599) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat false g p)
end)) g restPats)
in (match (_77_602) with
| (g, restMLPats) -> begin
(
# 525 "FStar.Extraction.ML.Term.fst"
let _77_610 = (let _166_222 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _77_2 -> (match (_77_2) with
| Some (x) -> begin
(x)::[]
end
| _77_607 -> begin
[]
end))))
in (FStar_All.pipe_right _166_222 FStar_List.split))
in (match (_77_610) with
| (mlPats, when_clauses) -> begin
(let _166_226 = (let _166_225 = (let _166_224 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _166_223 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_166_224, _166_223)))
in Some (_166_225))
in (g, _166_226))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 529 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 530 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _166_230 = if imp then begin
None
end else begin
(let _166_229 = (let _166_228 = (let _166_227 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_166_227))
in (_166_228, []))
in Some (_166_229))
end
in (g, _166_230))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 537 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 538 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _166_234 = if imp then begin
None
end else begin
(let _166_233 = (let _166_232 = (let _166_231 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_166_231))
in (_166_232, []))
in Some (_166_233))
end
in (g, _166_234))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_77_622) -> begin
(g, None)
end))
in (
# 544 "FStar.Extraction.ML.Term.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _77_635 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (
# 549 "FStar.Extraction.ML.Term.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _166_243 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_166_243))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(
# 558 "FStar.Extraction.ML.Term.fst"
let _77_650 = (extract_one_pat true g p)
in (match (_77_650) with
| (g, p) -> begin
(
# 559 "FStar.Extraction.ML.Term.fst"
let ps = (let _166_246 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _166_245 = (extract_one_pat true g x)
in (Prims.snd _166_245)))))
in (p)::_166_246)
in (
# 560 "FStar.Extraction.ML.Term.fst"
let _77_666 = (FStar_All.pipe_right ps (FStar_List.partition (fun _77_3 -> (match (_77_3) with
| (_77_655, _77_659::_77_657) -> begin
true
end
| _77_663 -> begin
false
end))))
in (match (_77_666) with
| (ps_when, rest) -> begin
(
# 561 "FStar.Extraction.ML.Term.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _77_669 -> (match (_77_669) with
| (x, whens) -> begin
(let _166_249 = (mk_when_clause whens)
in (x, _166_249))
end))))
in (
# 563 "FStar.Extraction.ML.Term.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _166_253 = (let _166_252 = (let _166_251 = (let _166_250 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_166_250))
in (_166_251, None))
in (_166_252)::ps)
in (g, _166_253))
end)
in res))
end)))
end))
end
| _77_675 -> begin
(
# 569 "FStar.Extraction.ML.Term.fst"
let _77_680 = (extract_one_pat false g p)
in (match (_77_680) with
| (g, (p, whens)) -> begin
(
# 570 "FStar.Extraction.ML.Term.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 589 "FStar.Extraction.ML.Term.fst"
let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 590 "FStar.Extraction.ML.Term.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _77_691, t1) -> begin
(
# 592 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _166_268 = (let _166_267 = (let _166_266 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _166_266))
in (_166_267)::more_args)
in (eta_args _166_268 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_77_697, _77_699) -> begin
((FStar_List.rev more_args), t)
end
| _77_703 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (
# 597 "FStar.Extraction.ML.Term.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_77_708, args), Some (FStar_Syntax_Syntax.Record_ctor (_77_713, fields))) -> begin
(
# 600 "FStar.Extraction.ML.Term.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 601 "FStar.Extraction.ML.Term.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _77_722 -> begin
e
end))
in (
# 605 "FStar.Extraction.ML.Term.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 606 "FStar.Extraction.ML.Term.fst"
let _77_728 = (eta_args [] residualType)
in (match (_77_728) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _166_277 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _166_277))
end
| _77_731 -> begin
(
# 610 "FStar.Extraction.ML.Term.fst"
let _77_734 = (FStar_List.unzip eargs)
in (match (_77_734) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 613 "FStar.Extraction.ML.Term.fst"
let body = (let _166_279 = (let _166_278 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _166_278))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _166_279))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _77_741 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_77_743, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _77_749; FStar_Extraction_ML_Syntax.loc = _77_747}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(
# 621 "FStar.Extraction.ML.Term.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 622 "FStar.Extraction.ML.Term.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 623 "FStar.Extraction.ML.Term.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _77_766 -> begin
(let _166_281 = (let _166_280 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_166_280, args))
in FStar_Extraction_ML_Syntax.MLE_App (_166_281))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _166_282 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_282))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _166_283 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_283))
end
| _77_806 -> begin
mlAppExpr
end)))))

# 639 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (
# 640 "FStar.Extraction.ML.Term.fst"
let _77_812 = (term_as_mlexpr' g t)
in (match (_77_812) with
| (e, tag, ty) -> begin
(erase g e ty tag)
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (
# 645 "FStar.Extraction.ML.Term.fst"
let _77_819 = (check_term_as_mlexpr' g t f ty)
in (match (_77_819) with
| (e, t) -> begin
(
# 646 "FStar.Extraction.ML.Term.fst"
let _77_824 = (erase g e t f)
in (match (_77_824) with
| (r, _77_822, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (
# 650 "FStar.Extraction.ML.Term.fst"
let _77_832 = (term_as_mlexpr g e0)
in (match (_77_832) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _166_306 = (maybe_coerce g e t ty)
in (_166_306, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (
# 656 "FStar.Extraction.ML.Term.fst"
let _77_836 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _166_312 = (let _166_311 = (FStar_Syntax_Print.tag_of_term top)
in (let _166_310 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _166_311 _166_310)))
in (FStar_Util.print_string _166_312))))
in (
# 657 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _166_314 = (let _166_313 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _166_313))
in (FStar_All.failwith _166_314))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 674 "FStar.Extraction.ML.Term.fst"
let _77_874 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_77_874) with
| (_77_870, ty, _77_873) -> begin
(
# 675 "FStar.Extraction.ML.Term.fst"
let ml_ty = (term_as_mlty g ty)
in (let _166_318 = (let _166_317 = (let _166_316 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _166_315 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_315)) _166_316))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _166_317))
in (_166_318, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_77_883), _77_886) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _77_891), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, t)
end
| ([], t) -> begin
(let _166_319 = (maybe_eta_data_and_project_record g qual t x)
in (_166_319, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _77_903 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(
# 696 "FStar.Extraction.ML.Term.fst"
let _77_911 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_911) with
| (bs, body) -> begin
(
# 697 "FStar.Extraction.ML.Term.fst"
let _77_914 = (binders_as_ml_binders g bs)
in (match (_77_914) with
| (ml_bs, env) -> begin
(
# 698 "FStar.Extraction.ML.Term.fst"
let _77_918 = (term_as_mlexpr env body)
in (match (_77_918) with
| (ml_body, f, t) -> begin
(
# 699 "FStar.Extraction.ML.Term.fst"
let _77_928 = (FStar_List.fold_right (fun _77_922 _77_925 -> (match ((_77_922, _77_925)) with
| ((_77_920, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_77_928) with
| (f, tfun) -> begin
(let _166_322 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_166_322, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_77_934) -> begin
(
# 707 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _77_938 -> begin
(
# 710 "FStar.Extraction.ML.Term.fst"
let rec extract_app = (fun is_data _77_943 _77_946 restArgs -> (match ((_77_943, _77_946)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _77_950) -> begin
(
# 718 "FStar.Extraction.ML.Term.fst"
let _77_961 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _166_331 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _166_331))
end else begin
(FStar_List.fold_left (fun _77_954 _77_957 -> (match ((_77_954, _77_957)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 724 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _166_335 = (let _166_334 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_166_334)::out_args)
in (((x, arg))::lbs, _166_335)))
end
end)) ([], []) mlargs_f)
end
in (match (_77_961) with
| (lbs, mlargs) -> begin
(
# 727 "FStar.Extraction.ML.Term.fst"
let app = (let _166_336 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _166_336))
in (
# 728 "FStar.Extraction.ML.Term.fst"
let l_app = (FStar_List.fold_right (fun _77_965 out -> (match (_77_965) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false (false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]) out))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _77_971)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _166_340 = (let _166_339 = (FStar_Extraction_ML_Util.join f f')
in (_166_339, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _166_340 rest))
end else begin
(let _166_345 = (let _166_344 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _166_343 = (FStar_Syntax_Print.term_to_string arg)
in (let _166_342 = (FStar_Syntax_Print.tag_of_term arg)
in (let _166_341 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _166_344 _166_343 _166_342 _166_341)))))
in (FStar_All.failwith _166_345))
end
end
| ((e0, _77_983)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 744 "FStar.Extraction.ML.Term.fst"
let _77_995 = (term_as_mlexpr g e0)
in (match (_77_995) with
| (e0, f0, tInferred) -> begin
(
# 745 "FStar.Extraction.ML.Term.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _166_347 = (let _166_346 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_166_346, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _166_347 rest)))
end))
end
| _77_998 -> begin
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
# 754 "FStar.Extraction.ML.Term.fst"
let extract_app_maybe_projector = (fun is_data mlhead _77_1007 args -> (match (_77_1007) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_77_1010)) -> begin
(
# 757 "FStar.Extraction.ML.Term.fst"
let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((_77_1019, Some (FStar_Syntax_Syntax.Implicit (_77_1021)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_77_1027, f', t)) -> begin
(let _166_362 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _166_362 t))
end
| _77_1034 -> begin
(args, f, t)
end))
in (
# 762 "FStar.Extraction.ML.Term.fst"
let _77_1038 = (remove_implicits args f t)
in (match (_77_1038) with
| (args, f, t) -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)))
end
| _77_1040 -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)
end))
in if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(
# 770 "FStar.Extraction.ML.Term.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 775 "FStar.Extraction.ML.Term.fst"
let _77_1061 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _77_1053 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_77_1061) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 776 "FStar.Extraction.ML.Term.fst"
let has_typ_apps = (match (args) with
| (a, _77_1066)::_77_1063 -> begin
(is_type g a)
end
| _77_1070 -> begin
false
end)
in (
# 780 "FStar.Extraction.ML.Term.fst"
let _77_1116 = (match (vars) with
| _77_1075::_77_1073 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _77_1078 -> begin
(
# 787 "FStar.Extraction.ML.Term.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 789 "FStar.Extraction.ML.Term.fst"
let _77_1082 = (FStar_Util.first_N n args)
in (match (_77_1082) with
| (prefix, rest) -> begin
(
# 791 "FStar.Extraction.ML.Term.fst"
let prefixAsMLTypes = (FStar_List.map (fun _77_1086 -> (match (_77_1086) with
| (x, _77_1085) -> begin
(term_as_mlty g x)
end)) prefix)
in (
# 793 "FStar.Extraction.ML.Term.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 794 "FStar.Extraction.ML.Term.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 796 "FStar.Extraction.ML.Term.fst"
let _77_1095 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _77_1095.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _77_1095.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _77_1101; FStar_Extraction_ML_Syntax.loc = _77_1099}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 797 "FStar.Extraction.ML.Term.fst"
let _77_1108 = head
in {FStar_Extraction_ML_Syntax.expr = _77_1108.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _77_1108.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _77_1111 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_77_1116) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _166_364 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_166_364, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _77_1119 -> begin
(extract_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _77_1121 -> begin
(
# 808 "FStar.Extraction.ML.Term.fst"
let _77_1125 = (term_as_mlexpr g head)
in (match (_77_1125) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head (f, t) args)
end))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(
# 814 "FStar.Extraction.ML.Term.fst"
let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (
# 817 "FStar.Extraction.ML.Term.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (
# 820 "FStar.Extraction.ML.Term.fst"
let _77_1142 = (check_term_as_mlexpr g e0 f t)
in (match (_77_1142) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(
# 824 "FStar.Extraction.ML.Term.fst"
let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (
# 825 "FStar.Extraction.ML.Term.fst"
let _77_1158 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(
# 830 "FStar.Extraction.ML.Term.fst"
let lb = (FStar_List.hd lbs)
in (
# 831 "FStar.Extraction.ML.Term.fst"
let x = (let _166_365 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _166_365))
in (
# 832 "FStar.Extraction.ML.Term.fst"
let lb = (
# 832 "FStar.Extraction.ML.Term.fst"
let _77_1152 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _77_1152.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _77_1152.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _77_1152.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _77_1152.FStar_Syntax_Syntax.lbdef})
in (
# 833 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_77_1158) with
| (lbs, e') -> begin
(
# 836 "FStar.Extraction.ML.Term.fst"
let maybe_generalize = (fun _77_1166 -> (match (_77_1166) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _77_1164; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 837 "FStar.Extraction.ML.Term.fst"
let f_e = (effect_as_etag g lbeff)
in (
# 838 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _166_368 = (FStar_List.hd bs)
in (FStar_All.pipe_right _166_368 (is_type_binder g))) -> begin
(
# 842 "FStar.Extraction.ML.Term.fst"
let _77_1175 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_1175) with
| (bs, c) -> begin
(
# 849 "FStar.Extraction.ML.Term.fst"
let _77_1185 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _166_370 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _166_370))
end)
in (match (_77_1185) with
| (tbinders, tbody) -> begin
(
# 854 "FStar.Extraction.ML.Term.fst"
let n_tbinders = (FStar_List.length tbinders)
in (
# 855 "FStar.Extraction.ML.Term.fst"
let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_1191) -> begin
(
# 858 "FStar.Extraction.ML.Term.fst"
let _77_1196 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_1196) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(
# 860 "FStar.Extraction.ML.Term.fst"
let _77_1199 = (FStar_Util.first_N n_tbinders bs)
in (match (_77_1199) with
| (targs, rest_args) -> begin
(
# 864 "FStar.Extraction.ML.Term.fst"
let expected_t = (
# 865 "FStar.Extraction.ML.Term.fst"
let s = (FStar_List.map2 (fun _77_1203 _77_1207 -> (match ((_77_1203, _77_1207)) with
| ((x, _77_1202), (y, _77_1206)) -> begin
(let _166_374 = (let _166_373 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _166_373))
in FStar_Syntax_Syntax.NT (_166_374))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (
# 868 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _77_1214 -> (match (_77_1214) with
| (a, _77_1213) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (
# 869 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty env expected_t)
in (
# 870 "FStar.Extraction.ML.Term.fst"
let polytype = (let _166_378 = (FStar_All.pipe_right targs (FStar_List.map (fun _77_1220 -> (match (_77_1220) with
| (x, _77_1219) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_166_378, expected_t))
in (
# 871 "FStar.Extraction.ML.Term.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _77_1224 -> begin
false
end)
in (
# 874 "FStar.Extraction.ML.Term.fst"
let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (
# 875 "FStar.Extraction.ML.Term.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _77_1229 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| _77_1232 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _77_1234 -> begin
(
# 906 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 909 "FStar.Extraction.ML.Term.fst"
let check_lb = (fun env _77_1249 -> (match (_77_1249) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 910 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _77_1254 -> (match (_77_1254) with
| (a, _77_1253) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (
# 911 "FStar.Extraction.ML.Term.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 912 "FStar.Extraction.ML.Term.fst"
let _77_1260 = (check_term_as_mlexpr env e f expected_t)
in (match (_77_1260) with
| (e, _77_1259) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (
# 916 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 918 "FStar.Extraction.ML.Term.fst"
let _77_1284 = (FStar_List.fold_right (fun lb _77_1265 -> (match (_77_1265) with
| (env, lbs) -> begin
(
# 919 "FStar.Extraction.ML.Term.fst"
let _77_1278 = lb
in (match (_77_1278) with
| (lbname, _77_1268, (t, (_77_1271, polytype)), add_unit, _77_1277) -> begin
(
# 920 "FStar.Extraction.ML.Term.fst"
let _77_1281 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_77_1281) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_77_1284) with
| (env_body, lbs) -> begin
(
# 923 "FStar.Extraction.ML.Term.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 925 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 927 "FStar.Extraction.ML.Term.fst"
let _77_1290 = (term_as_mlexpr env_body e')
in (match (_77_1290) with
| (e', f', t') -> begin
(
# 929 "FStar.Extraction.ML.Term.fst"
let f = (let _166_388 = (let _166_387 = (FStar_List.map Prims.fst lbs)
in (f')::_166_387)
in (FStar_Extraction_ML_Util.join_l _166_388))
in (let _166_393 = (let _166_392 = (let _166_390 = (let _166_389 = (FStar_List.map Prims.snd lbs)
in (is_rec, _166_389))
in (mk_MLE_Let top_level _166_390 e'))
in (let _166_391 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _166_392 _166_391)))
in (_166_393, f, t')))
end))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(
# 934 "FStar.Extraction.ML.Term.fst"
let _77_1299 = (term_as_mlexpr g scrutinee)
in (match (_77_1299) with
| (e, f_e, t_e) -> begin
(
# 935 "FStar.Extraction.ML.Term.fst"
let _77_1303 = (check_pats_for_ite pats)
in (match (_77_1303) with
| (b, then_e, else_e) -> begin
(
# 936 "FStar.Extraction.ML.Term.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 940 "FStar.Extraction.ML.Term.fst"
let _77_1315 = (term_as_mlexpr g then_e)
in (match (_77_1315) with
| (then_mle, f_then, t_then) -> begin
(
# 941 "FStar.Extraction.ML.Term.fst"
let _77_1319 = (term_as_mlexpr g else_e)
in (match (_77_1319) with
| (else_mle, f_else, t_else) -> begin
(
# 942 "FStar.Extraction.ML.Term.fst"
let _77_1322 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_77_1322) with
| (t_branch, maybe_lift) -> begin
(let _166_424 = (let _166_422 = (let _166_421 = (let _166_420 = (maybe_lift then_mle t_then)
in (let _166_419 = (let _166_418 = (maybe_lift else_mle t_else)
in Some (_166_418))
in (e, _166_420, _166_419)))
in FStar_Extraction_ML_Syntax.MLE_If (_166_421))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _166_422))
in (let _166_423 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_166_424, _166_423, t_branch)))
end))
end))
end))
end
| _77_1324 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 953 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (
# 954 "FStar.Extraction.ML.Term.fst"
let _77_1329 = (FStar_Syntax_Subst.open_branch br)
in (match (_77_1329) with
| (pat, when_opt, branch) -> begin
(
# 955 "FStar.Extraction.ML.Term.fst"
let _77_1332 = (extract_pat g pat)
in (match (_77_1332) with
| (env, p) -> begin
(
# 956 "FStar.Extraction.ML.Term.fst"
let _77_1343 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 959 "FStar.Extraction.ML.Term.fst"
let _77_1339 = (term_as_mlexpr env w)
in (match (_77_1339) with
| (w, f_w, t_w) -> begin
(
# 960 "FStar.Extraction.ML.Term.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_77_1343) with
| (when_opt, f_when) -> begin
(
# 962 "FStar.Extraction.ML.Term.fst"
let _77_1347 = (term_as_mlexpr env branch)
in (match (_77_1347) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _77_1350 -> (match (_77_1350) with
| (p, wopt) -> begin
(
# 965 "FStar.Extraction.ML.Term.fst"
let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
end))))
end))
end))
end))
end)))))
in (match (mlbranches) with
| [] -> begin
(
# 970 "FStar.Extraction.ML.Term.fst"
let _77_1359 = (let _166_428 = (let _166_427 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _166_427))
in (FStar_All.pipe_left FStar_Util.right _166_428))
in (match (_77_1359) with
| (fw, _77_1356, _77_1358) -> begin
(let _166_433 = (let _166_432 = (let _166_431 = (let _166_430 = (let _166_429 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_166_429)::[])
in (fw, _166_430))
in FStar_Extraction_ML_Syntax.MLE_App (_166_431))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _166_432))
in (_166_433, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_77_1362, _77_1364, (_77_1366, f_first, t_first))::rest -> begin
(
# 977 "FStar.Extraction.ML.Term.fst"
let _77_1392 = (FStar_List.fold_left (fun _77_1374 _77_1384 -> (match ((_77_1374, _77_1384)) with
| ((topt, f), (_77_1376, _77_1378, (_77_1380, f_branch, t_branch))) -> begin
(
# 981 "FStar.Extraction.ML.Term.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 982 "FStar.Extraction.ML.Term.fst"
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
in (match (_77_1392) with
| (topt, f_match) -> begin
(
# 995 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _77_1403 -> (match (_77_1403) with
| (p, (wopt, _77_1396), (b, _77_1400, t)) -> begin
(
# 996 "FStar.Extraction.ML.Term.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_77_1406) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 1002 "FStar.Extraction.ML.Term.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _166_437 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_166_437, f_match, t_match))))
end))
end))
end)
end))
end))
end))))

# 1010 "FStar.Extraction.ML.Term.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 1010 "FStar.Extraction.ML.Term.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 1011 "FStar.Extraction.ML.Term.fst"
let _77_1416 = (FStar_Util.incr c)
in (let _166_440 = (FStar_ST.read c)
in (x, _166_440)))))

# 1013 "FStar.Extraction.ML.Term.fst"
let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 1015 "FStar.Extraction.ML.Term.fst"
let _77_1424 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_77_1424) with
| (_77_1422, fstar_disc_type) -> begin
(
# 1016 "FStar.Extraction.ML.Term.fst"
let wildcards = (match ((let _166_447 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _166_447.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _77_1427) -> begin
(let _166_451 = (FStar_All.pipe_right binders (FStar_List.filter (fun _77_4 -> (match (_77_4) with
| (_77_1432, Some (FStar_Syntax_Syntax.Implicit (_77_1434))) -> begin
true
end
| _77_1439 -> begin
false
end))))
in (FStar_All.pipe_right _166_451 (FStar_List.map (fun _77_1440 -> (let _166_450 = (fresh "_")
in (_166_450, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _77_1443 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 1027 "FStar.Extraction.ML.Term.fst"
let mlid = (fresh "_discr_")
in (
# 1028 "FStar.Extraction.ML.Term.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 1031 "FStar.Extraction.ML.Term.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 1032 "FStar.Extraction.ML.Term.fst"
let discrBody = (let _166_466 = (let _166_465 = (let _166_464 = (let _166_463 = (let _166_462 = (let _166_461 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _166_460 = (let _166_459 = (let _166_455 = (let _166_453 = (let _166_452 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_166_452, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_166_453))
in (let _166_454 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_166_455, None, _166_454)))
in (let _166_458 = (let _166_457 = (let _166_456 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _166_456))
in (_166_457)::[])
in (_166_459)::_166_458))
in (_166_461, _166_460)))
in FStar_Extraction_ML_Syntax.MLE_Match (_166_462))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_463))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _166_464))
in FStar_Extraction_ML_Syntax.MLE_Fun (_166_465))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _166_466))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




