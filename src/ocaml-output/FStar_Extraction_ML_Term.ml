
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
let _67_17 = (let _146_28 = (let _146_27 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _146_27 msg))
in (FStar_All.pipe_left FStar_Util.print_string _146_28))
in (FStar_All.failwith msg)))

# 62 "FStar.Extraction.ML.Term.fst"
let err_uninst = (fun env t _67_23 -> (match (_67_23) with
| (vars, ty) -> begin
(let _146_36 = (let _146_35 = (FStar_Syntax_Print.term_to_string t)
in (let _146_34 = (let _146_32 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _146_32 (FStar_String.concat ", ")))
in (let _146_33 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _146_35 _146_34 _146_33))))
in (fail t.FStar_Syntax_Syntax.pos _146_36))
end))

# 68 "FStar.Extraction.ML.Term.fst"
let err_ill_typed_application = (fun t args ty -> (let _146_44 = (let _146_43 = (FStar_Syntax_Print.term_to_string t)
in (let _146_42 = (let _146_41 = (FStar_All.pipe_right args (FStar_List.map (fun _67_30 -> (match (_67_30) with
| (x, _67_29) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _146_41 (FStar_String.concat " ")))
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _146_43 _146_42)))
in (fail t.FStar_Syntax_Syntax.pos _146_44)))

# 74 "FStar.Extraction.ML.Term.fst"
let err_value_restriction = (fun t -> (fail t.FStar_Syntax_Syntax.pos "Refusing to generalize because of the value restriction"))

# 77 "FStar.Extraction.ML.Term.fst"
let err_unexpected_eff = (fun t f0 f1 -> (let _146_50 = (let _146_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _146_49 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _146_50)))

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
| Some (_67_44, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (
# 92 "FStar.Extraction.ML.Term.fst"
let _67_49 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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
let predecessor = (fun t _67_1 -> (match (_67_1) with
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
| FStar_Syntax_Syntax.Tm_delayed (_67_65) -> begin
(let _146_74 = (let _146_73 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _146_73))
in (FStar_All.failwith _146_74))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_67_69) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _67_77; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_67_74); FStar_Syntax_Syntax.fv_qual = _67_72}) -> begin
(
# 135 "FStar.Extraction.ML.Term.fst"
let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (
# 136 "FStar.Extraction.ML.Term.fst"
let _67_82 = (FStar_Extraction_ML_UEnv.debug env (fun _67_81 -> (match (()) with
| () -> begin
(let _146_77 = (FStar_Syntax_Print.term_to_string t)
in (let _146_76 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _146_77 _146_76)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _146_78 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _146_78))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _146_79 = (level env t)
in (FStar_All.pipe_left predecessor _146_79))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _67_105, _67_107) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_67_111) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _67_115) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _67_120) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _67_134) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_67_138, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_67_143, branches) -> begin
(match (branches) with
| (_67_150, _67_152, e)::_67_148 -> begin
(level env e)
end
| _67_157 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _67_160) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _67_165) -> begin
(level env head)
end))))

# 190 "FStar.Extraction.ML.Term.fst"
let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _67_172 -> begin
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
let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _146_88 = (FStar_Syntax_Subst.compress t)
in _146_88.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _67_198 -> begin
false
end))

# 207 "FStar.Extraction.ML.Term.fst"
let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _146_91 = (FStar_Syntax_Subst.compress t)
in _146_91.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _67_219 -> (match (_67_219) with
| (te, _67_218) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _67_232 -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Record (_67_253, fields) -> begin
(FStar_Util.for_all (fun _67_260 -> (match (_67_260) with
| (_67_258, e) -> begin
(is_ml_value e)
end)) fields)
end
| _67_262 -> begin
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
| _67_275 -> begin
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
let unit_binder : FStar_Syntax_Syntax.binder = (let _146_104 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _146_104))

# 261 "FStar.Extraction.ML.Term.fst"
let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (
# 264 "FStar.Extraction.ML.Term.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 267 "FStar.Extraction.ML.Term.fst"
let _67_282 = (FStar_List.hd l)
in (match (_67_282) with
| (p1, w1, e1) -> begin
(
# 268 "FStar.Extraction.ML.Term.fst"
let _67_286 = (let _146_107 = (FStar_List.tl l)
in (FStar_List.hd _146_107))
in (match (_67_286) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _67_306 -> begin
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
| _67_327 -> begin
(
# 322 "FStar.Extraction.ML.Term.fst"
let _67_329 = (FStar_Extraction_ML_UEnv.debug g (fun _67_328 -> (match (()) with
| () -> begin
(let _146_137 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _146_136 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _146_135 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _146_137 _146_136 _146_135))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))

# 331 "FStar.Extraction.ML.Term.fst"
let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_67_334, t) -> begin
t
end
| _67_339 -> begin
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
(let _146_158 = (let _146_157 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _146_157))
in (FStar_All.failwith _146_158))
end
| FStar_Syntax_Syntax.Tm_uvar (_67_357) -> begin
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
let _67_393 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_67_393) with
| (bs, c) -> begin
(
# 379 "FStar.Extraction.ML.Term.fst"
let _67_396 = (binders_as_ml_binders env bs)
in (match (_67_396) with
| (mlbs, env) -> begin
(
# 380 "FStar.Extraction.ML.Term.fst"
let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (
# 381 "FStar.Extraction.ML.Term.fst"
let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (
# 382 "FStar.Extraction.ML.Term.fst"
let _67_409 = (FStar_List.fold_right (fun _67_402 _67_405 -> (match ((_67_402, _67_405)) with
| ((_67_400, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_67_409) with
| (_67_407, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 388 "FStar.Extraction.ML.Term.fst"
let res = (match ((let _146_161 = (FStar_Syntax_Subst.compress head)
in _146_161.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _146_162 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _146_162))
end
| _67_423 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _67_428) -> begin
(
# 404 "FStar.Extraction.ML.Term.fst"
let _67_433 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_67_433) with
| (bs, ty) -> begin
(
# 405 "FStar.Extraction.ML.Term.fst"
let _67_436 = (binders_as_ml_binders env bs)
in (match (_67_436) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _67_450 -> (match (_67_450) with
| (a, _67_449) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (
# 418 "FStar.Extraction.ML.Term.fst"
let _67_456 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_67_456) with
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
let _67_462 = (FStar_Util.first_N n_args formals)
in (match (_67_462) with
| (_67_460, rest) -> begin
(let _146_169 = (FStar_List.map (fun _67_463 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _146_169))
end))
end else begin
mlargs
end)
in (let _146_171 = (let _146_170 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _146_170))
in FStar_Extraction_ML_Syntax.MLTY_Named (_146_171))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (
# 429 "FStar.Extraction.ML.Term.fst"
let _67_481 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _67_470 b -> (match (_67_470) with
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
let ml_b = (let _146_176 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_146_176, FStar_Extraction_ML_Syntax.ml_unit_ty))
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
let ml_b = (let _146_177 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_146_177, t))
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_67_481) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))

# 452 "FStar.Extraction.ML.Term.fst"
let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _67_491 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_67_493, fns)) -> begin
(
# 459 "FStar.Extraction.ML.Term.fst"
let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (
# 460 "FStar.Extraction.ML.Term.fst"
let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _67_501 -> begin
p
end)
end)
end
| _67_503 -> begin
p
end))

# 470 "FStar.Extraction.ML.Term.fst"
let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 471 "FStar.Extraction.ML.Term.fst"
let rec extract_one_pat = (fun disjunctive_pat imp g p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_67_512) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 477 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (
# 478 "FStar.Extraction.ML.Term.fst"
let when_clause = (let _146_202 = (let _146_201 = (let _146_200 = (let _146_199 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _146_198 = (let _146_197 = (let _146_196 = (let _146_195 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _146_194 -> FStar_Extraction_ML_Syntax.MLE_Const (_146_194)) _146_195))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _146_196))
in (_146_197)::[])
in (_146_199)::_146_198))
in (FStar_Extraction_ML_Util.bigint_equality, _146_200))
in FStar_Extraction_ML_Syntax.MLE_App (_146_201))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _146_202))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(let _146_206 = (let _146_205 = (let _146_204 = (let _146_203 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_146_203))
in (_146_204, []))
in Some (_146_205))
in (g, _146_206))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(
# 486 "FStar.Extraction.ML.Term.fst"
let _67_541 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _67_528; FStar_Extraction_ML_Syntax.loc = _67_526}, ttys, _67_534) -> begin
(n, ttys)
end
| _67_538 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_67_541) with
| (d, tys) -> begin
(
# 489 "FStar.Extraction.ML.Term.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 490 "FStar.Extraction.ML.Term.fst"
let _67_545 = (FStar_Util.first_N nTyVars pats)
in (match (_67_545) with
| (tysVarPats, restPats) -> begin
(
# 491 "FStar.Extraction.ML.Term.fst"
let _67_552 = (FStar_Util.fold_map (fun g _67_549 -> (match (_67_549) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat true g p)
end)) g tysVarPats)
in (match (_67_552) with
| (g, tyMLPats) -> begin
(
# 492 "FStar.Extraction.ML.Term.fst"
let _67_559 = (FStar_Util.fold_map (fun g _67_556 -> (match (_67_556) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat false g p)
end)) g restPats)
in (match (_67_559) with
| (g, restMLPats) -> begin
(
# 493 "FStar.Extraction.ML.Term.fst"
let _67_567 = (let _146_212 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _67_2 -> (match (_67_2) with
| Some (x) -> begin
(x)::[]
end
| _67_564 -> begin
[]
end))))
in (FStar_All.pipe_right _146_212 FStar_List.split))
in (match (_67_567) with
| (mlPats, when_clauses) -> begin
(let _146_216 = (let _146_215 = (let _146_214 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _146_213 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_146_214, _146_213)))
in Some (_146_215))
in (g, _146_216))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 497 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 498 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _146_220 = if imp then begin
None
end else begin
(let _146_219 = (let _146_218 = (let _146_217 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_146_217))
in (_146_218, []))
in Some (_146_219))
end
in (g, _146_220))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 505 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 506 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _146_224 = if imp then begin
None
end else begin
(let _146_223 = (let _146_222 = (let _146_221 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_146_221))
in (_146_222, []))
in Some (_146_223))
end
in (g, _146_224))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_67_579) -> begin
(g, None)
end))
in (
# 512 "FStar.Extraction.ML.Term.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _67_592 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (
# 517 "FStar.Extraction.ML.Term.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _146_233 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_146_233))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(
# 526 "FStar.Extraction.ML.Term.fst"
let _67_607 = (extract_one_pat true g p)
in (match (_67_607) with
| (g, p) -> begin
(
# 527 "FStar.Extraction.ML.Term.fst"
let ps = (let _146_236 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _146_235 = (extract_one_pat true g x)
in (Prims.snd _146_235)))))
in (p)::_146_236)
in (
# 528 "FStar.Extraction.ML.Term.fst"
let _67_623 = (FStar_All.pipe_right ps (FStar_List.partition (fun _67_3 -> (match (_67_3) with
| (_67_612, _67_616::_67_614) -> begin
true
end
| _67_620 -> begin
false
end))))
in (match (_67_623) with
| (ps_when, rest) -> begin
(
# 529 "FStar.Extraction.ML.Term.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _67_626 -> (match (_67_626) with
| (x, whens) -> begin
(let _146_239 = (mk_when_clause whens)
in (x, _146_239))
end))))
in (
# 531 "FStar.Extraction.ML.Term.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _146_243 = (let _146_242 = (let _146_241 = (let _146_240 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_146_240))
in (_146_241, None))
in (_146_242)::ps)
in (g, _146_243))
end)
in res))
end)))
end))
end
| _67_632 -> begin
(
# 537 "FStar.Extraction.ML.Term.fst"
let _67_637 = (extract_one_pat false g p)
in (match (_67_637) with
| (g, (p, whens)) -> begin
(
# 538 "FStar.Extraction.ML.Term.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 557 "FStar.Extraction.ML.Term.fst"
let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 558 "FStar.Extraction.ML.Term.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _67_648, t1) -> begin
(
# 560 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _146_258 = (let _146_257 = (let _146_256 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _146_256))
in (_146_257)::more_args)
in (eta_args _146_258 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_67_654, _67_656) -> begin
((FStar_List.rev more_args), t)
end
| _67_660 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (
# 565 "FStar.Extraction.ML.Term.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_67_665, args), Some (FStar_Syntax_Syntax.Record_ctor (_67_670, fields))) -> begin
(
# 568 "FStar.Extraction.ML.Term.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 569 "FStar.Extraction.ML.Term.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _67_679 -> begin
e
end))
in (
# 573 "FStar.Extraction.ML.Term.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 574 "FStar.Extraction.ML.Term.fst"
let _67_685 = (eta_args [] residualType)
in (match (_67_685) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _146_267 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _146_267))
end
| _67_688 -> begin
(
# 578 "FStar.Extraction.ML.Term.fst"
let _67_691 = (FStar_List.unzip eargs)
in (match (_67_691) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 581 "FStar.Extraction.ML.Term.fst"
let body = (let _146_269 = (let _146_268 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _146_268))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _146_269))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _67_698 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_67_700, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _67_706; FStar_Extraction_ML_Syntax.loc = _67_704}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(
# 589 "FStar.Extraction.ML.Term.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 590 "FStar.Extraction.ML.Term.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 591 "FStar.Extraction.ML.Term.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _67_723 -> begin
(let _146_271 = (let _146_270 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_146_270, args))
in FStar_Extraction_ML_Syntax.MLE_App (_146_271))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _146_272 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _146_272))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _146_273 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _146_273))
end
| _67_763 -> begin
mlAppExpr
end)))))

# 607 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (
# 608 "FStar.Extraction.ML.Term.fst"
let _67_769 = (term_as_mlexpr' g t)
in (match (_67_769) with
| (e, tag, ty) -> begin
(erase g e ty tag)
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (
# 613 "FStar.Extraction.ML.Term.fst"
let _67_776 = (check_term_as_mlexpr' g t f ty)
in (match (_67_776) with
| (e, t) -> begin
(
# 614 "FStar.Extraction.ML.Term.fst"
let _67_781 = (erase g e t f)
in (match (_67_781) with
| (r, _67_779, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (
# 618 "FStar.Extraction.ML.Term.fst"
let _67_789 = (term_as_mlexpr g e0)
in (match (_67_789) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _146_296 = (maybe_coerce g e t ty)
in (_146_296, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (
# 624 "FStar.Extraction.ML.Term.fst"
let _67_793 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _146_302 = (let _146_301 = (FStar_Syntax_Print.tag_of_term top)
in (let _146_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _146_301 _146_300)))
in (FStar_Util.print_string _146_302))))
in (
# 625 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _146_304 = (let _146_303 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _146_303))
in (FStar_All.failwith _146_304))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 642 "FStar.Extraction.ML.Term.fst"
let _67_831 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_67_831) with
| (_67_827, ty, _67_830) -> begin
(
# 643 "FStar.Extraction.ML.Term.fst"
let ml_ty = (term_as_mlty g ty)
in (let _146_308 = (let _146_307 = (let _146_306 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _146_305 -> FStar_Extraction_ML_Syntax.MLE_Const (_146_305)) _146_306))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _146_307))
in (_146_308, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_67_840), _67_843) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _67_848), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _146_309 = (maybe_eta_data_and_project_record g qual t x)
in (_146_309, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _67_857 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(
# 663 "FStar.Extraction.ML.Term.fst"
let _67_865 = (FStar_Syntax_Subst.open_term bs body)
in (match (_67_865) with
| (bs, body) -> begin
(
# 664 "FStar.Extraction.ML.Term.fst"
let _67_868 = (binders_as_ml_binders g bs)
in (match (_67_868) with
| (ml_bs, env) -> begin
(
# 665 "FStar.Extraction.ML.Term.fst"
let _67_872 = (term_as_mlexpr env body)
in (match (_67_872) with
| (ml_body, f, t) -> begin
(
# 666 "FStar.Extraction.ML.Term.fst"
let _67_882 = (FStar_List.fold_right (fun _67_876 _67_879 -> (match ((_67_876, _67_879)) with
| ((_67_874, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_67_882) with
| (f, tfun) -> begin
(let _146_312 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_146_312, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_67_888) -> begin
(
# 674 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _67_892 -> begin
(
# 677 "FStar.Extraction.ML.Term.fst"
let rec extract_app = (fun is_data _67_897 _67_900 restArgs -> (match ((_67_897, _67_900)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _67_904) -> begin
(
# 685 "FStar.Extraction.ML.Term.fst"
let _67_915 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _146_321 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _146_321))
end else begin
(FStar_List.fold_left (fun _67_908 _67_911 -> (match ((_67_908, _67_911)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 691 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _146_325 = (let _146_324 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_146_324)::out_args)
in (((x, arg))::lbs, _146_325)))
end
end)) ([], []) mlargs_f)
end
in (match (_67_915) with
| (lbs, mlargs) -> begin
(
# 694 "FStar.Extraction.ML.Term.fst"
let app = (let _146_326 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _146_326))
in (
# 695 "FStar.Extraction.ML.Term.fst"
let l_app = (FStar_List.fold_right (fun _67_919 out -> (match (_67_919) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _67_925)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _146_330 = (let _146_329 = (FStar_Extraction_ML_Util.join f f')
in (_146_329, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _146_330 rest))
end else begin
(let _146_335 = (let _146_334 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _146_333 = (FStar_Syntax_Print.term_to_string arg)
in (let _146_332 = (FStar_Syntax_Print.tag_of_term arg)
in (let _146_331 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _146_334 _146_333 _146_332 _146_331)))))
in (FStar_All.failwith _146_335))
end
end
| ((e0, _67_937)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 712 "FStar.Extraction.ML.Term.fst"
let _67_949 = (term_as_mlexpr g e0)
in (match (_67_949) with
| (e0, f0, tInferred) -> begin
(
# 713 "FStar.Extraction.ML.Term.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _146_337 = (let _146_336 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_146_336, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _146_337 rest)))
end))
end
| _67_952 -> begin
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
# 722 "FStar.Extraction.ML.Term.fst"
let extract_app_maybe_projector = (fun is_data mlhead _67_961 args -> (match (_67_961) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_67_964)) -> begin
(
# 725 "FStar.Extraction.ML.Term.fst"
let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((_67_973, Some (FStar_Syntax_Syntax.Implicit (_67_975)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_67_981, f', t)) -> begin
(let _146_352 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _146_352 t))
end
| _67_988 -> begin
(args, f, t)
end))
in (
# 730 "FStar.Extraction.ML.Term.fst"
let _67_992 = (remove_implicits args f t)
in (match (_67_992) with
| (args, f, t) -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)))
end
| _67_994 -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)
end))
in if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(
# 738 "FStar.Extraction.ML.Term.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 743 "FStar.Extraction.ML.Term.fst"
let _67_1015 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _67_1007 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_67_1015) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 744 "FStar.Extraction.ML.Term.fst"
let has_typ_apps = (match (args) with
| (a, _67_1020)::_67_1017 -> begin
(is_type g a)
end
| _67_1024 -> begin
false
end)
in (
# 748 "FStar.Extraction.ML.Term.fst"
let _67_1070 = (match (vars) with
| _67_1029::_67_1027 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _67_1032 -> begin
(
# 755 "FStar.Extraction.ML.Term.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 757 "FStar.Extraction.ML.Term.fst"
let _67_1036 = (FStar_Util.first_N n args)
in (match (_67_1036) with
| (prefix, rest) -> begin
(
# 759 "FStar.Extraction.ML.Term.fst"
let prefixAsMLTypes = (FStar_List.map (fun _67_1040 -> (match (_67_1040) with
| (x, _67_1039) -> begin
(term_as_mlty g x)
end)) prefix)
in (
# 761 "FStar.Extraction.ML.Term.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 762 "FStar.Extraction.ML.Term.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 764 "FStar.Extraction.ML.Term.fst"
let _67_1049 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _67_1049.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _67_1049.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _67_1055; FStar_Extraction_ML_Syntax.loc = _67_1053}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 765 "FStar.Extraction.ML.Term.fst"
let _67_1062 = head
in {FStar_Extraction_ML_Syntax.expr = _67_1062.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _67_1062.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _67_1065 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_67_1070) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _146_354 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_146_354, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _67_1073 -> begin
(extract_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _67_1075 -> begin
(
# 776 "FStar.Extraction.ML.Term.fst"
let _67_1079 = (term_as_mlexpr g head)
in (match (_67_1079) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head (f, t) args)
end))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(
# 782 "FStar.Extraction.ML.Term.fst"
let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (
# 785 "FStar.Extraction.ML.Term.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (
# 788 "FStar.Extraction.ML.Term.fst"
let _67_1096 = (check_term_as_mlexpr g e0 f t)
in (match (_67_1096) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(
# 792 "FStar.Extraction.ML.Term.fst"
let _67_1111 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(
# 797 "FStar.Extraction.ML.Term.fst"
let lb = (FStar_List.hd lbs)
in (
# 798 "FStar.Extraction.ML.Term.fst"
let x = (let _146_355 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _146_355))
in (
# 799 "FStar.Extraction.ML.Term.fst"
let lb = (
# 799 "FStar.Extraction.ML.Term.fst"
let _67_1105 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _67_1105.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _67_1105.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _67_1105.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _67_1105.FStar_Syntax_Syntax.lbdef})
in (
# 800 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_67_1111) with
| (lbs, e') -> begin
(
# 803 "FStar.Extraction.ML.Term.fst"
let maybe_generalize = (fun _67_1119 -> (match (_67_1119) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _67_1117; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 804 "FStar.Extraction.ML.Term.fst"
let f_e = (effect_as_etag g lbeff)
in (
# 805 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _146_358 = (FStar_List.hd bs)
in (FStar_All.pipe_right _146_358 (is_type_binder g))) -> begin
(
# 809 "FStar.Extraction.ML.Term.fst"
let _67_1128 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_67_1128) with
| (bs, c) -> begin
(
# 816 "FStar.Extraction.ML.Term.fst"
let _67_1138 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _146_360 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _146_360))
end)
in (match (_67_1138) with
| (tbinders, tbody) -> begin
(
# 821 "FStar.Extraction.ML.Term.fst"
let n_tbinders = (FStar_List.length tbinders)
in (
# 822 "FStar.Extraction.ML.Term.fst"
let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _67_1144) -> begin
(
# 825 "FStar.Extraction.ML.Term.fst"
let _67_1149 = (FStar_Syntax_Subst.open_term bs body)
in (match (_67_1149) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(
# 827 "FStar.Extraction.ML.Term.fst"
let _67_1152 = (FStar_Util.first_N n_tbinders bs)
in (match (_67_1152) with
| (targs, rest_args) -> begin
(
# 831 "FStar.Extraction.ML.Term.fst"
let expected_t = (
# 832 "FStar.Extraction.ML.Term.fst"
let s = (FStar_List.map2 (fun _67_1156 _67_1160 -> (match ((_67_1156, _67_1160)) with
| ((x, _67_1155), (y, _67_1159)) -> begin
(let _146_364 = (let _146_363 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _146_363))
in FStar_Syntax_Syntax.NT (_146_364))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (
# 835 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _67_1167 -> (match (_67_1167) with
| (a, _67_1166) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (
# 836 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty env expected_t)
in (
# 837 "FStar.Extraction.ML.Term.fst"
let polytype = (let _146_368 = (FStar_All.pipe_right targs (FStar_List.map (fun _67_1173 -> (match (_67_1173) with
| (x, _67_1172) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_146_368, expected_t))
in (
# 838 "FStar.Extraction.ML.Term.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _67_1177 -> begin
false
end)
in (
# 841 "FStar.Extraction.ML.Term.fst"
let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (
# 842 "FStar.Extraction.ML.Term.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _67_1182 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| _67_1185 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _67_1187 -> begin
(
# 873 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 876 "FStar.Extraction.ML.Term.fst"
let check_lb = (fun env _67_1202 -> (match (_67_1202) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 877 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _67_1207 -> (match (_67_1207) with
| (a, _67_1206) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (
# 878 "FStar.Extraction.ML.Term.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 879 "FStar.Extraction.ML.Term.fst"
let _67_1213 = (check_term_as_mlexpr env e f expected_t)
in (match (_67_1213) with
| (e, _67_1212) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (
# 883 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 885 "FStar.Extraction.ML.Term.fst"
let _67_1237 = (FStar_List.fold_right (fun lb _67_1218 -> (match (_67_1218) with
| (env, lbs) -> begin
(
# 886 "FStar.Extraction.ML.Term.fst"
let _67_1231 = lb
in (match (_67_1231) with
| (lbname, _67_1221, (t, (_67_1224, polytype)), add_unit, _67_1230) -> begin
(
# 887 "FStar.Extraction.ML.Term.fst"
let _67_1234 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_67_1234) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_67_1237) with
| (env_body, lbs) -> begin
(
# 890 "FStar.Extraction.ML.Term.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 892 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 894 "FStar.Extraction.ML.Term.fst"
let _67_1243 = (term_as_mlexpr env_body e')
in (match (_67_1243) with
| (e', f', t') -> begin
(
# 896 "FStar.Extraction.ML.Term.fst"
let f = (let _146_378 = (let _146_377 = (FStar_List.map Prims.fst lbs)
in (f')::_146_377)
in (FStar_Extraction_ML_Util.join_l _146_378))
in (let _146_384 = (let _146_383 = (let _146_381 = (let _146_380 = (let _146_379 = (FStar_List.map Prims.snd lbs)
in (is_rec, _146_379))
in (_146_380, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_146_381))
in (let _146_382 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _146_383 _146_382)))
in (_146_384, f, t')))
end))))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(
# 901 "FStar.Extraction.ML.Term.fst"
let _67_1252 = (term_as_mlexpr g scrutinee)
in (match (_67_1252) with
| (e, f_e, t_e) -> begin
(
# 902 "FStar.Extraction.ML.Term.fst"
let _67_1256 = (check_pats_for_ite pats)
in (match (_67_1256) with
| (b, then_e, else_e) -> begin
(
# 903 "FStar.Extraction.ML.Term.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 907 "FStar.Extraction.ML.Term.fst"
let _67_1268 = (term_as_mlexpr g then_e)
in (match (_67_1268) with
| (then_mle, f_then, t_then) -> begin
(
# 908 "FStar.Extraction.ML.Term.fst"
let _67_1272 = (term_as_mlexpr g else_e)
in (match (_67_1272) with
| (else_mle, f_else, t_else) -> begin
(
# 909 "FStar.Extraction.ML.Term.fst"
let _67_1275 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_67_1275) with
| (t_branch, maybe_lift) -> begin
(let _146_415 = (let _146_413 = (let _146_412 = (let _146_411 = (maybe_lift then_mle t_then)
in (let _146_410 = (let _146_409 = (maybe_lift else_mle t_else)
in Some (_146_409))
in (e, _146_411, _146_410)))
in FStar_Extraction_ML_Syntax.MLE_If (_146_412))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _146_413))
in (let _146_414 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_146_415, _146_414, t_branch)))
end))
end))
end))
end
| _67_1277 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 920 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (
# 921 "FStar.Extraction.ML.Term.fst"
let _67_1282 = (FStar_Syntax_Subst.open_branch br)
in (match (_67_1282) with
| (pat, when_opt, branch) -> begin
(
# 922 "FStar.Extraction.ML.Term.fst"
let _67_1285 = (extract_pat g pat)
in (match (_67_1285) with
| (env, p) -> begin
(
# 923 "FStar.Extraction.ML.Term.fst"
let _67_1296 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 926 "FStar.Extraction.ML.Term.fst"
let _67_1292 = (term_as_mlexpr env w)
in (match (_67_1292) with
| (w, f_w, t_w) -> begin
(
# 927 "FStar.Extraction.ML.Term.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_67_1296) with
| (when_opt, f_when) -> begin
(
# 929 "FStar.Extraction.ML.Term.fst"
let _67_1300 = (term_as_mlexpr env branch)
in (match (_67_1300) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _67_1303 -> (match (_67_1303) with
| (p, wopt) -> begin
(
# 932 "FStar.Extraction.ML.Term.fst"
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
# 937 "FStar.Extraction.ML.Term.fst"
let _67_1312 = (let _146_419 = (let _146_418 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _146_418))
in (FStar_All.pipe_left FStar_Util.right _146_419))
in (match (_67_1312) with
| (fw, _67_1309, _67_1311) -> begin
(let _146_424 = (let _146_423 = (let _146_422 = (let _146_421 = (let _146_420 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_146_420)::[])
in (fw, _146_421))
in FStar_Extraction_ML_Syntax.MLE_App (_146_422))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _146_423))
in (_146_424, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_67_1315, _67_1317, (_67_1319, f_first, t_first))::rest -> begin
(
# 944 "FStar.Extraction.ML.Term.fst"
let _67_1345 = (FStar_List.fold_left (fun _67_1327 _67_1337 -> (match ((_67_1327, _67_1337)) with
| ((topt, f), (_67_1329, _67_1331, (_67_1333, f_branch, t_branch))) -> begin
(
# 948 "FStar.Extraction.ML.Term.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 949 "FStar.Extraction.ML.Term.fst"
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
in (match (_67_1345) with
| (topt, f_match) -> begin
(
# 962 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _67_1356 -> (match (_67_1356) with
| (p, (wopt, _67_1349), (b, _67_1353, t)) -> begin
(
# 963 "FStar.Extraction.ML.Term.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_67_1359) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 969 "FStar.Extraction.ML.Term.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _146_428 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_146_428, f_match, t_match))))
end))
end))
end)
end))
end))
end))))

# 977 "FStar.Extraction.ML.Term.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 977 "FStar.Extraction.ML.Term.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 978 "FStar.Extraction.ML.Term.fst"
let _67_1369 = (FStar_Util.incr c)
in (let _146_431 = (FStar_ST.read c)
in (x, _146_431)))))

# 980 "FStar.Extraction.ML.Term.fst"
let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 982 "FStar.Extraction.ML.Term.fst"
let _67_1377 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_67_1377) with
| (_67_1375, fstar_disc_type) -> begin
(
# 983 "FStar.Extraction.ML.Term.fst"
let wildcards = (match ((let _146_438 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _146_438.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _67_1380) -> begin
(let _146_442 = (FStar_All.pipe_right binders (FStar_List.filter (fun _67_4 -> (match (_67_4) with
| (_67_1385, Some (FStar_Syntax_Syntax.Implicit (_67_1387))) -> begin
true
end
| _67_1392 -> begin
false
end))))
in (FStar_All.pipe_right _146_442 (FStar_List.map (fun _67_1393 -> (let _146_441 = (fresh "_")
in (_146_441, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _67_1396 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 994 "FStar.Extraction.ML.Term.fst"
let mlid = (fresh "_discr_")
in (
# 995 "FStar.Extraction.ML.Term.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 998 "FStar.Extraction.ML.Term.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 999 "FStar.Extraction.ML.Term.fst"
let discrBody = (let _146_457 = (let _146_456 = (let _146_455 = (let _146_454 = (let _146_453 = (let _146_452 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _146_451 = (let _146_450 = (let _146_446 = (let _146_444 = (let _146_443 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_146_443, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_146_444))
in (let _146_445 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_146_446, None, _146_445)))
in (let _146_449 = (let _146_448 = (let _146_447 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _146_447))
in (_146_448)::[])
in (_146_450)::_146_449))
in (_146_452, _146_451)))
in FStar_Extraction_ML_Syntax.MLE_Match (_146_453))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _146_454))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _146_455))
in FStar_Extraction_ML_Syntax.MLE_Fun (_146_456))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _146_457))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




