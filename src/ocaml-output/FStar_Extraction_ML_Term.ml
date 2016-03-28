
open Prims
# 34 "FStar.Extraction.ML.Term.fst"
let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))

# 48 "FStar.Extraction.ML.Term.fst"
let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))

# 49 "FStar.Extraction.ML.Term.fst"
let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))

# 50 "FStar.Extraction.ML.Term.fst"
let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))

# 53 "FStar.Extraction.ML.Term.fst"
let fail = (fun r msg -> (
# 59 "FStar.Extraction.ML.Term.fst"
let _73_17 = (let _158_28 = (let _158_27 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _158_27 msg))
in (FStar_All.pipe_left FStar_Util.print_string _158_28))
in (FStar_All.failwith msg)))

# 60 "FStar.Extraction.ML.Term.fst"
let err_uninst = (fun env t _73_23 -> (match (_73_23) with
| (vars, ty) -> begin
(let _158_36 = (let _158_35 = (FStar_Syntax_Print.term_to_string t)
in (let _158_34 = (let _158_32 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _158_32 (FStar_String.concat ", ")))
in (let _158_33 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _158_35 _158_34 _158_33))))
in (fail t.FStar_Syntax_Syntax.pos _158_36))
end))

# 66 "FStar.Extraction.ML.Term.fst"
let err_ill_typed_application = (fun t args ty -> (let _158_44 = (let _158_43 = (FStar_Syntax_Print.term_to_string t)
in (let _158_42 = (let _158_41 = (FStar_All.pipe_right args (FStar_List.map (fun _73_30 -> (match (_73_30) with
| (x, _73_29) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _158_41 (FStar_String.concat " ")))
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _158_43 _158_42)))
in (fail t.FStar_Syntax_Syntax.pos _158_44)))

# 71 "FStar.Extraction.ML.Term.fst"
let err_value_restriction = (fun t -> (fail t.FStar_Syntax_Syntax.pos "Refusing to generalize because of the value restriction"))

# 75 "FStar.Extraction.ML.Term.fst"
let err_unexpected_eff = (fun t f0 f1 -> (let _158_50 = (let _158_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _158_49 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _158_50)))

# 78 "FStar.Extraction.ML.Term.fst"
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
| Some (_73_44, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (
# 92 "FStar.Extraction.ML.Term.fst"
let _73_49 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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

# 100 "FStar.Extraction.ML.Term.fst"
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

# 109 "FStar.Extraction.ML.Term.fst"
let predecessor = (fun t _73_1 -> (match (_73_1) with
| Term_level -> begin
Term_level
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))

# 114 "FStar.Extraction.ML.Term.fst"
let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (
# 120 "FStar.Extraction.ML.Term.fst"
let predecessor = (fun l -> (predecessor t l))
in (
# 121 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 122 "FStar.Extraction.ML.Term.fst"
let _73_66 = (FStar_Extraction_ML_UEnv.debug env (fun _73_64 -> (let _158_72 = (FStar_Syntax_Print.term_to_string t)
in (let _158_71 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _158_72 _158_71)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_73_69) -> begin
(let _158_77 = (let _158_76 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _158_76))
in (FStar_All.failwith _158_77))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_73_73) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _73_81; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_73_78); FStar_Syntax_Syntax.fv_qual = _73_76}) -> begin
(let _158_78 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (level env _158_78))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _158_79 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _158_79))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _158_80 = (level env t)
in (FStar_All.pipe_left predecessor _158_80))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _73_105, _73_107) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_73_111) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _73_115) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _73_120) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _73_134) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_73_138, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_73_143, branches) -> begin
(match (branches) with
| (_73_150, _73_152, e)::_73_148 -> begin
(level env e)
end
| _73_157 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _73_160) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _73_165) -> begin
(level env head)
end)))))

# 184 "FStar.Extraction.ML.Term.fst"
let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _73_172 -> begin
true
end))

# 190 "FStar.Extraction.ML.Term.fst"
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

# 196 "FStar.Extraction.ML.Term.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _158_89 = (FStar_Syntax_Subst.compress t)
in _158_89.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _73_198 -> begin
false
end))

# 201 "FStar.Extraction.ML.Term.fst"
let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _158_92 = (FStar_Syntax_Subst.compress t)
in _158_92.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _73_219 -> (match (_73_219) with
| (te, _73_218) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _73_232 -> begin
false
end))

# 228 "FStar.Extraction.ML.Term.fst"
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_73_253, fields) -> begin
(FStar_Util.for_all (fun _73_260 -> (match (_73_260) with
| (_73_258, e) -> begin
(is_ml_value e)
end)) fields)
end
| _73_262 -> begin
false
end))

# 239 "FStar.Extraction.ML.Term.fst"
let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (
# 244 "FStar.Extraction.ML.Term.fst"
let rec aux = (fun bs t copt -> (
# 245 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _73_275 -> begin
(
# 249 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))

# 253 "FStar.Extraction.ML.Term.fst"
let unit_binder : FStar_Syntax_Syntax.binder = (let _158_105 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _158_105))

# 255 "FStar.Extraction.ML.Term.fst"
let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (
# 262 "FStar.Extraction.ML.Term.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 265 "FStar.Extraction.ML.Term.fst"
let _73_282 = (FStar_List.hd l)
in (match (_73_282) with
| (p1, w1, e1) -> begin
(
# 266 "FStar.Extraction.ML.Term.fst"
let _73_286 = (let _158_108 = (FStar_List.tl l)
in (FStar_List.hd _158_108))
in (match (_73_286) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _73_306 -> begin
def
end)
end))
end))
end))

# 275 "FStar.Extraction.ML.Term.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 296 "FStar.Extraction.ML.Term.fst"
let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))

# 302 "FStar.Extraction.ML.Term.fst"
let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (
# 307 "FStar.Extraction.ML.Term.fst"
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

# 311 "FStar.Extraction.ML.Term.fst"
let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (
# 316 "FStar.Extraction.ML.Term.fst"
let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _73_327 -> begin
(
# 320 "FStar.Extraction.ML.Term.fst"
let _73_329 = (FStar_Extraction_ML_UEnv.debug g (fun _73_328 -> (match (()) with
| () -> begin
(let _158_138 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _158_137 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _158_136 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _158_138 _158_137 _158_136))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))

# 324 "FStar.Extraction.ML.Term.fst"
let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_73_334, t) -> begin
t
end
| _73_339 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))

# 332 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (
# 349 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (
# 353 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _158_159 = (let _158_158 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _158_158))
in (FStar_All.failwith _158_159))
end
| FStar_Syntax_Syntax.Tm_uvar (_73_357) -> begin
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
# 376 "FStar.Extraction.ML.Term.fst"
let _73_393 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_73_393) with
| (bs, c) -> begin
(
# 377 "FStar.Extraction.ML.Term.fst"
let _73_396 = (binders_as_ml_binders env bs)
in (match (_73_396) with
| (mlbs, env) -> begin
(
# 378 "FStar.Extraction.ML.Term.fst"
let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (
# 379 "FStar.Extraction.ML.Term.fst"
let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (
# 380 "FStar.Extraction.ML.Term.fst"
let _73_409 = (FStar_List.fold_right (fun _73_402 _73_405 -> (match ((_73_402, _73_405)) with
| ((_73_400, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_73_409) with
| (_73_407, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 386 "FStar.Extraction.ML.Term.fst"
let res = (match ((let _158_162 = (FStar_Syntax_Subst.compress head)
in _158_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _158_163 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _158_163))
end
| _73_423 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _73_428) -> begin
(
# 402 "FStar.Extraction.ML.Term.fst"
let _73_433 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_73_433) with
| (bs, ty) -> begin
(
# 403 "FStar.Extraction.ML.Term.fst"
let _73_436 = (binders_as_ml_binders env bs)
in (match (_73_436) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _73_450 -> (match (_73_450) with
| (a, _73_449) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (
# 416 "FStar.Extraction.ML.Term.fst"
let _73_456 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_73_456) with
| (formals, t) -> begin
(
# 417 "FStar.Extraction.ML.Term.fst"
let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (
# 418 "FStar.Extraction.ML.Term.fst"
let mlargs = (
# 419 "FStar.Extraction.ML.Term.fst"
let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(
# 421 "FStar.Extraction.ML.Term.fst"
let _73_462 = (FStar_Util.first_N n_args formals)
in (match (_73_462) with
| (_73_460, rest) -> begin
(let _158_170 = (FStar_List.map (fun _73_463 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _158_170))
end))
end else begin
mlargs
end)
in (let _158_172 = (let _158_171 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _158_171))
in FStar_Extraction_ML_Syntax.MLTY_Named (_158_172))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (
# 427 "FStar.Extraction.ML.Term.fst"
let _73_481 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _73_470 b -> (match (_73_470) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(
# 430 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 431 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 432 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _158_177 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_158_177, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(
# 435 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 436 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (
# 437 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (
# 438 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _158_178 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_158_178, t))
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_73_481) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))

# 442 "FStar.Extraction.ML.Term.fst"
let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _73_491 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_73_493, fns)) -> begin
(
# 457 "FStar.Extraction.ML.Term.fst"
let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (
# 458 "FStar.Extraction.ML.Term.fst"
let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _73_501 -> begin
p
end)
end)
end
| _73_503 -> begin
p
end))

# 462 "FStar.Extraction.ML.Term.fst"
let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 469 "FStar.Extraction.ML.Term.fst"
let rec extract_one_pat = (fun disjunctive_pat imp g p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_73_512) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 475 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (
# 476 "FStar.Extraction.ML.Term.fst"
let when_clause = (let _158_203 = (let _158_202 = (let _158_201 = (let _158_200 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _158_199 = (let _158_198 = (let _158_197 = (let _158_196 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _158_195 -> FStar_Extraction_ML_Syntax.MLE_Const (_158_195)) _158_196))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _158_197))
in (_158_198)::[])
in (_158_200)::_158_199))
in (FStar_Extraction_ML_Util.bigint_equality, _158_201))
in FStar_Extraction_ML_Syntax.MLE_App (_158_202))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _158_203))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(let _158_207 = (let _158_206 = (let _158_205 = (let _158_204 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_158_204))
in (_158_205, []))
in Some (_158_206))
in (g, _158_207))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(
# 484 "FStar.Extraction.ML.Term.fst"
let _73_541 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _73_528; FStar_Extraction_ML_Syntax.loc = _73_526}, ttys, _73_534) -> begin
(n, ttys)
end
| _73_538 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_73_541) with
| (d, tys) -> begin
(
# 487 "FStar.Extraction.ML.Term.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 488 "FStar.Extraction.ML.Term.fst"
let _73_545 = (FStar_Util.first_N nTyVars pats)
in (match (_73_545) with
| (tysVarPats, restPats) -> begin
(
# 489 "FStar.Extraction.ML.Term.fst"
let _73_552 = (FStar_Util.fold_map (fun g _73_549 -> (match (_73_549) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat true g p)
end)) g tysVarPats)
in (match (_73_552) with
| (g, tyMLPats) -> begin
(
# 490 "FStar.Extraction.ML.Term.fst"
let _73_559 = (FStar_Util.fold_map (fun g _73_556 -> (match (_73_556) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat false g p)
end)) g restPats)
in (match (_73_559) with
| (g, restMLPats) -> begin
(
# 491 "FStar.Extraction.ML.Term.fst"
let _73_567 = (let _158_213 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _73_2 -> (match (_73_2) with
| Some (x) -> begin
(x)::[]
end
| _73_564 -> begin
[]
end))))
in (FStar_All.pipe_right _158_213 FStar_List.split))
in (match (_73_567) with
| (mlPats, when_clauses) -> begin
(let _158_217 = (let _158_216 = (let _158_215 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _158_214 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_158_215, _158_214)))
in Some (_158_216))
in (g, _158_217))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 495 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 496 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _158_221 = if imp then begin
None
end else begin
(let _158_220 = (let _158_219 = (let _158_218 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_158_218))
in (_158_219, []))
in Some (_158_220))
end
in (g, _158_221))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 503 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 504 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _158_225 = if imp then begin
None
end else begin
(let _158_224 = (let _158_223 = (let _158_222 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_158_222))
in (_158_223, []))
in Some (_158_224))
end
in (g, _158_225))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_73_579) -> begin
(g, None)
end))
in (
# 510 "FStar.Extraction.ML.Term.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _73_592 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (
# 515 "FStar.Extraction.ML.Term.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _158_234 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_158_234))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(
# 524 "FStar.Extraction.ML.Term.fst"
let _73_607 = (extract_one_pat true g p)
in (match (_73_607) with
| (g, p) -> begin
(
# 525 "FStar.Extraction.ML.Term.fst"
let ps = (let _158_237 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _158_236 = (extract_one_pat true g x)
in (Prims.snd _158_236)))))
in (p)::_158_237)
in (
# 526 "FStar.Extraction.ML.Term.fst"
let _73_623 = (FStar_All.pipe_right ps (FStar_List.partition (fun _73_3 -> (match (_73_3) with
| (_73_612, _73_616::_73_614) -> begin
true
end
| _73_620 -> begin
false
end))))
in (match (_73_623) with
| (ps_when, rest) -> begin
(
# 527 "FStar.Extraction.ML.Term.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _73_626 -> (match (_73_626) with
| (x, whens) -> begin
(let _158_240 = (mk_when_clause whens)
in (x, _158_240))
end))))
in (
# 529 "FStar.Extraction.ML.Term.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _158_244 = (let _158_243 = (let _158_242 = (let _158_241 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_158_241))
in (_158_242, None))
in (_158_243)::ps)
in (g, _158_244))
end)
in res))
end)))
end))
end
| _73_632 -> begin
(
# 535 "FStar.Extraction.ML.Term.fst"
let _73_637 = (extract_one_pat false g p)
in (match (_73_637) with
| (g, (p, whens)) -> begin
(
# 536 "FStar.Extraction.ML.Term.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 537 "FStar.Extraction.ML.Term.fst"
let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 556 "FStar.Extraction.ML.Term.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _73_648, t1) -> begin
(
# 558 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _158_259 = (let _158_258 = (let _158_257 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _158_257))
in (_158_258)::more_args)
in (eta_args _158_259 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_73_654, _73_656) -> begin
((FStar_List.rev more_args), t)
end
| _73_660 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (
# 563 "FStar.Extraction.ML.Term.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_73_665, args), Some (FStar_Syntax_Syntax.Record_ctor (_73_670, fields))) -> begin
(
# 566 "FStar.Extraction.ML.Term.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 567 "FStar.Extraction.ML.Term.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _73_679 -> begin
e
end))
in (
# 571 "FStar.Extraction.ML.Term.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 572 "FStar.Extraction.ML.Term.fst"
let _73_685 = (eta_args [] residualType)
in (match (_73_685) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _158_268 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _158_268))
end
| _73_688 -> begin
(
# 576 "FStar.Extraction.ML.Term.fst"
let _73_691 = (FStar_List.unzip eargs)
in (match (_73_691) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 579 "FStar.Extraction.ML.Term.fst"
let body = (let _158_270 = (let _158_269 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _158_269))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _158_270))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _73_698 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_73_700, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _73_706; FStar_Extraction_ML_Syntax.loc = _73_704}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(
# 587 "FStar.Extraction.ML.Term.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 588 "FStar.Extraction.ML.Term.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 589 "FStar.Extraction.ML.Term.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _73_723 -> begin
(let _158_272 = (let _158_271 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_158_271, args))
in FStar_Extraction_ML_Syntax.MLE_App (_158_272))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _158_273 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _158_273))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _158_274 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _158_274))
end
| _73_763 -> begin
mlAppExpr
end)))))

# 602 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (
# 606 "FStar.Extraction.ML.Term.fst"
let _73_769 = (term_as_mlexpr' g t)
in (match (_73_769) with
| (e, tag, ty) -> begin
(erase g e ty tag)
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (
# 611 "FStar.Extraction.ML.Term.fst"
let _73_776 = (check_term_as_mlexpr' g t f ty)
in (match (_73_776) with
| (e, t) -> begin
(
# 612 "FStar.Extraction.ML.Term.fst"
let _73_781 = (erase g e t f)
in (match (_73_781) with
| (r, _73_779, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (
# 616 "FStar.Extraction.ML.Term.fst"
let _73_789 = (term_as_mlexpr g e0)
in (match (_73_789) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _158_297 = (maybe_coerce g e t ty)
in (_158_297, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (
# 622 "FStar.Extraction.ML.Term.fst"
let _73_793 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _158_303 = (let _158_302 = (FStar_Syntax_Print.tag_of_term top)
in (let _158_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _158_302 _158_301)))
in (FStar_Util.print_string _158_303))))
in (
# 623 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _158_305 = (let _158_304 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _158_304))
in (FStar_All.failwith _158_305))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 640 "FStar.Extraction.ML.Term.fst"
let _73_829 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_73_829) with
| (ty, _73_828) -> begin
(
# 641 "FStar.Extraction.ML.Term.fst"
let ml_ty = (term_as_mlty g ty)
in (let _158_309 = (let _158_308 = (let _158_307 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _158_306 -> FStar_Extraction_ML_Syntax.MLE_Const (_158_306)) _158_307))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _158_308))
in (_158_309, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_73_838), _73_841) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _73_846), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _158_310 = (maybe_eta_data_and_project_record g qual t x)
in (_158_310, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _73_855 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(
# 661 "FStar.Extraction.ML.Term.fst"
let _73_863 = (FStar_Syntax_Subst.open_term bs body)
in (match (_73_863) with
| (bs, body) -> begin
(
# 662 "FStar.Extraction.ML.Term.fst"
let _73_866 = (binders_as_ml_binders g bs)
in (match (_73_866) with
| (ml_bs, env) -> begin
(
# 663 "FStar.Extraction.ML.Term.fst"
let _73_870 = (term_as_mlexpr env body)
in (match (_73_870) with
| (ml_body, f, t) -> begin
(
# 664 "FStar.Extraction.ML.Term.fst"
let _73_880 = (FStar_List.fold_right (fun _73_874 _73_877 -> (match ((_73_874, _73_877)) with
| ((_73_872, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_73_880) with
| (f, tfun) -> begin
(let _158_313 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_158_313, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_73_886) -> begin
(
# 672 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _73_890 -> begin
(
# 675 "FStar.Extraction.ML.Term.fst"
let rec extract_app = (fun is_data _73_895 _73_898 restArgs -> (match ((_73_895, _73_898)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _73_902) -> begin
(
# 683 "FStar.Extraction.ML.Term.fst"
let _73_913 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _158_322 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _158_322))
end else begin
(FStar_List.fold_left (fun _73_906 _73_909 -> (match ((_73_906, _73_909)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 689 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _158_326 = (let _158_325 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_158_325)::out_args)
in (((x, arg))::lbs, _158_326)))
end
end)) ([], []) mlargs_f)
end
in (match (_73_913) with
| (lbs, mlargs) -> begin
(
# 692 "FStar.Extraction.ML.Term.fst"
let app = (let _158_327 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _158_327))
in (
# 693 "FStar.Extraction.ML.Term.fst"
let l_app = (FStar_List.fold_right (fun _73_917 out -> (match (_73_917) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _73_923)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _158_331 = (let _158_330 = (FStar_Extraction_ML_Util.join f f')
in (_158_330, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _158_331 rest))
end else begin
(let _158_336 = (let _158_335 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _158_334 = (FStar_Syntax_Print.term_to_string arg)
in (let _158_333 = (FStar_Syntax_Print.tag_of_term arg)
in (let _158_332 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _158_335 _158_334 _158_333 _158_332)))))
in (FStar_All.failwith _158_336))
end
end
| ((e0, _73_935)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 710 "FStar.Extraction.ML.Term.fst"
let _73_947 = (term_as_mlexpr g e0)
in (match (_73_947) with
| (e0, f0, tInferred) -> begin
(
# 711 "FStar.Extraction.ML.Term.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _158_338 = (let _158_337 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_158_337, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _158_338 rest)))
end))
end
| _73_950 -> begin
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
# 720 "FStar.Extraction.ML.Term.fst"
let extract_app_maybe_projector = (fun is_data mlhead _73_959 args -> (match (_73_959) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_73_962)) -> begin
(
# 723 "FStar.Extraction.ML.Term.fst"
let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((_73_971, Some (FStar_Syntax_Syntax.Implicit (_73_973)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_73_979, f', t)) -> begin
(let _158_353 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _158_353 t))
end
| _73_986 -> begin
(args, f, t)
end))
in (
# 728 "FStar.Extraction.ML.Term.fst"
let _73_990 = (remove_implicits args f t)
in (match (_73_990) with
| (args, f, t) -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)))
end
| _73_992 -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)
end))
in if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(
# 736 "FStar.Extraction.ML.Term.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 741 "FStar.Extraction.ML.Term.fst"
let _73_1013 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _73_1005 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_73_1013) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 742 "FStar.Extraction.ML.Term.fst"
let has_typ_apps = (match (args) with
| (a, _73_1018)::_73_1015 -> begin
(is_type g a)
end
| _73_1022 -> begin
false
end)
in (
# 746 "FStar.Extraction.ML.Term.fst"
let _73_1068 = (match (vars) with
| _73_1027::_73_1025 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _73_1030 -> begin
(
# 753 "FStar.Extraction.ML.Term.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 755 "FStar.Extraction.ML.Term.fst"
let _73_1034 = (FStar_Util.first_N n args)
in (match (_73_1034) with
| (prefix, rest) -> begin
(
# 757 "FStar.Extraction.ML.Term.fst"
let prefixAsMLTypes = (FStar_List.map (fun _73_1038 -> (match (_73_1038) with
| (x, _73_1037) -> begin
(term_as_mlty g x)
end)) prefix)
in (
# 759 "FStar.Extraction.ML.Term.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 760 "FStar.Extraction.ML.Term.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 762 "FStar.Extraction.ML.Term.fst"
let _73_1047 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _73_1047.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _73_1047.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _73_1053; FStar_Extraction_ML_Syntax.loc = _73_1051}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 763 "FStar.Extraction.ML.Term.fst"
let _73_1060 = head
in {FStar_Extraction_ML_Syntax.expr = _73_1060.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _73_1060.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _73_1063 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_73_1068) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _158_355 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_158_355, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _73_1071 -> begin
(extract_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _73_1073 -> begin
(
# 774 "FStar.Extraction.ML.Term.fst"
let _73_1077 = (term_as_mlexpr g head)
in (match (_73_1077) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head (f, t) args)
end))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, t, f) -> begin
(
# 780 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty g t)
in (
# 781 "FStar.Extraction.ML.Term.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (
# 784 "FStar.Extraction.ML.Term.fst"
let _73_1090 = (check_term_as_mlexpr g e0 f t)
in (match (_73_1090) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(
# 788 "FStar.Extraction.ML.Term.fst"
let _73_1105 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(
# 793 "FStar.Extraction.ML.Term.fst"
let lb = (FStar_List.hd lbs)
in (
# 794 "FStar.Extraction.ML.Term.fst"
let x = (let _158_356 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _158_356))
in (
# 795 "FStar.Extraction.ML.Term.fst"
let lb = (
# 795 "FStar.Extraction.ML.Term.fst"
let _73_1099 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _73_1099.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _73_1099.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _73_1099.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _73_1099.FStar_Syntax_Syntax.lbdef})
in (
# 796 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_73_1105) with
| (lbs, e') -> begin
(
# 799 "FStar.Extraction.ML.Term.fst"
let maybe_generalize = (fun _73_1113 -> (match (_73_1113) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _73_1111; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 800 "FStar.Extraction.ML.Term.fst"
let f_e = (effect_as_etag g lbeff)
in (
# 801 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _158_359 = (FStar_List.hd bs)
in (FStar_All.pipe_right _158_359 (is_type_binder g))) -> begin
(
# 805 "FStar.Extraction.ML.Term.fst"
let _73_1122 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_73_1122) with
| (bs, c) -> begin
(
# 812 "FStar.Extraction.ML.Term.fst"
let _73_1132 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _158_361 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _158_361))
end)
in (match (_73_1132) with
| (tbinders, tbody) -> begin
(
# 817 "FStar.Extraction.ML.Term.fst"
let n_tbinders = (FStar_List.length tbinders)
in (
# 818 "FStar.Extraction.ML.Term.fst"
let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _73_1138) -> begin
(
# 821 "FStar.Extraction.ML.Term.fst"
let _73_1143 = (FStar_Syntax_Subst.open_term bs body)
in (match (_73_1143) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(
# 823 "FStar.Extraction.ML.Term.fst"
let _73_1146 = (FStar_Util.first_N n_tbinders bs)
in (match (_73_1146) with
| (targs, rest_args) -> begin
(
# 827 "FStar.Extraction.ML.Term.fst"
let expected_t = (
# 828 "FStar.Extraction.ML.Term.fst"
let s = (FStar_List.map2 (fun _73_1150 _73_1154 -> (match ((_73_1150, _73_1154)) with
| ((x, _73_1149), (y, _73_1153)) -> begin
(let _158_365 = (let _158_364 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _158_364))
in FStar_Syntax_Syntax.NT (_158_365))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (
# 831 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _73_1161 -> (match (_73_1161) with
| (a, _73_1160) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (
# 832 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty env expected_t)
in (
# 833 "FStar.Extraction.ML.Term.fst"
let polytype = (let _158_369 = (FStar_All.pipe_right targs (FStar_List.map (fun _73_1167 -> (match (_73_1167) with
| (x, _73_1166) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_158_369, expected_t))
in (
# 834 "FStar.Extraction.ML.Term.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _73_1171 -> begin
false
end)
in (
# 837 "FStar.Extraction.ML.Term.fst"
let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (
# 838 "FStar.Extraction.ML.Term.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _73_1176 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| _73_1179 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _73_1181 -> begin
(
# 869 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 872 "FStar.Extraction.ML.Term.fst"
let check_lb = (fun env _73_1196 -> (match (_73_1196) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 873 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _73_1201 -> (match (_73_1201) with
| (a, _73_1200) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (
# 874 "FStar.Extraction.ML.Term.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 875 "FStar.Extraction.ML.Term.fst"
let _73_1207 = (check_term_as_mlexpr env e f expected_t)
in (match (_73_1207) with
| (e, _73_1206) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (
# 879 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 881 "FStar.Extraction.ML.Term.fst"
let _73_1231 = (FStar_List.fold_right (fun lb _73_1212 -> (match (_73_1212) with
| (env, lbs) -> begin
(
# 882 "FStar.Extraction.ML.Term.fst"
let _73_1225 = lb
in (match (_73_1225) with
| (lbname, _73_1215, (t, (_73_1218, polytype)), add_unit, _73_1224) -> begin
(
# 883 "FStar.Extraction.ML.Term.fst"
let _73_1228 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_73_1228) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_73_1231) with
| (env_body, lbs) -> begin
(
# 886 "FStar.Extraction.ML.Term.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 888 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 890 "FStar.Extraction.ML.Term.fst"
let _73_1237 = (term_as_mlexpr env_body e')
in (match (_73_1237) with
| (e', f', t') -> begin
(
# 892 "FStar.Extraction.ML.Term.fst"
let f = (let _158_379 = (let _158_378 = (FStar_List.map Prims.fst lbs)
in (f')::_158_378)
in (FStar_Extraction_ML_Util.join_l _158_379))
in (let _158_385 = (let _158_384 = (let _158_382 = (let _158_381 = (let _158_380 = (FStar_List.map Prims.snd lbs)
in (is_rec, _158_380))
in (_158_381, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_158_382))
in (let _158_383 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _158_384 _158_383)))
in (_158_385, f, t')))
end))))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(
# 897 "FStar.Extraction.ML.Term.fst"
let _73_1246 = (term_as_mlexpr g scrutinee)
in (match (_73_1246) with
| (e, f_e, t_e) -> begin
(
# 898 "FStar.Extraction.ML.Term.fst"
let _73_1250 = (check_pats_for_ite pats)
in (match (_73_1250) with
| (b, then_e, else_e) -> begin
(
# 899 "FStar.Extraction.ML.Term.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 903 "FStar.Extraction.ML.Term.fst"
let _73_1262 = (term_as_mlexpr g then_e)
in (match (_73_1262) with
| (then_mle, f_then, t_then) -> begin
(
# 904 "FStar.Extraction.ML.Term.fst"
let _73_1266 = (term_as_mlexpr g else_e)
in (match (_73_1266) with
| (else_mle, f_else, t_else) -> begin
(
# 905 "FStar.Extraction.ML.Term.fst"
let _73_1269 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_73_1269) with
| (t_branch, maybe_lift) -> begin
(let _158_416 = (let _158_414 = (let _158_413 = (let _158_412 = (maybe_lift then_mle t_then)
in (let _158_411 = (let _158_410 = (maybe_lift else_mle t_else)
in Some (_158_410))
in (e, _158_412, _158_411)))
in FStar_Extraction_ML_Syntax.MLE_If (_158_413))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _158_414))
in (let _158_415 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_158_416, _158_415, t_branch)))
end))
end))
end))
end
| _73_1271 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 916 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (
# 917 "FStar.Extraction.ML.Term.fst"
let _73_1276 = (FStar_Syntax_Subst.open_branch br)
in (match (_73_1276) with
| (pat, when_opt, branch) -> begin
(
# 918 "FStar.Extraction.ML.Term.fst"
let _73_1279 = (extract_pat g pat)
in (match (_73_1279) with
| (env, p) -> begin
(
# 919 "FStar.Extraction.ML.Term.fst"
let _73_1290 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 922 "FStar.Extraction.ML.Term.fst"
let _73_1286 = (term_as_mlexpr env w)
in (match (_73_1286) with
| (w, f_w, t_w) -> begin
(
# 923 "FStar.Extraction.ML.Term.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_73_1290) with
| (when_opt, f_when) -> begin
(
# 925 "FStar.Extraction.ML.Term.fst"
let _73_1294 = (term_as_mlexpr env branch)
in (match (_73_1294) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _73_1297 -> (match (_73_1297) with
| (p, wopt) -> begin
(
# 928 "FStar.Extraction.ML.Term.fst"
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
# 933 "FStar.Extraction.ML.Term.fst"
let _73_1306 = (let _158_420 = (let _158_419 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _158_419))
in (FStar_All.pipe_left FStar_Util.right _158_420))
in (match (_73_1306) with
| (fw, _73_1303, _73_1305) -> begin
(let _158_425 = (let _158_424 = (let _158_423 = (let _158_422 = (let _158_421 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_158_421)::[])
in (fw, _158_422))
in FStar_Extraction_ML_Syntax.MLE_App (_158_423))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _158_424))
in (_158_425, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_73_1309, _73_1311, (_73_1313, f_first, t_first))::rest -> begin
(
# 940 "FStar.Extraction.ML.Term.fst"
let _73_1339 = (FStar_List.fold_left (fun _73_1321 _73_1331 -> (match ((_73_1321, _73_1331)) with
| ((topt, f), (_73_1323, _73_1325, (_73_1327, f_branch, t_branch))) -> begin
(
# 944 "FStar.Extraction.ML.Term.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 945 "FStar.Extraction.ML.Term.fst"
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
in (match (_73_1339) with
| (topt, f_match) -> begin
(
# 958 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _73_1350 -> (match (_73_1350) with
| (p, (wopt, _73_1343), (b, _73_1347, t)) -> begin
(
# 959 "FStar.Extraction.ML.Term.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_73_1353) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 965 "FStar.Extraction.ML.Term.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _158_429 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_158_429, f_match, t_match))))
end))
end))
end)
end))
end))
end))))

# 969 "FStar.Extraction.ML.Term.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 973 "FStar.Extraction.ML.Term.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 974 "FStar.Extraction.ML.Term.fst"
let _73_1363 = (FStar_Util.incr c)
in (let _158_432 = (FStar_ST.read c)
in (x, _158_432)))))

# 974 "FStar.Extraction.ML.Term.fst"
let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 978 "FStar.Extraction.ML.Term.fst"
let _73_1371 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_73_1371) with
| (_73_1369, fstar_disc_type) -> begin
(
# 979 "FStar.Extraction.ML.Term.fst"
let wildcards = (match ((let _158_439 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _158_439.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _73_1374) -> begin
(let _158_443 = (FStar_All.pipe_right binders (FStar_List.filter (fun _73_4 -> (match (_73_4) with
| (_73_1379, Some (FStar_Syntax_Syntax.Implicit (_73_1381))) -> begin
true
end
| _73_1386 -> begin
false
end))))
in (FStar_All.pipe_right _158_443 (FStar_List.map (fun _73_1387 -> (let _158_442 = (fresh "_")
in (_158_442, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _73_1390 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 990 "FStar.Extraction.ML.Term.fst"
let mlid = (fresh "_discr_")
in (
# 991 "FStar.Extraction.ML.Term.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 994 "FStar.Extraction.ML.Term.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 995 "FStar.Extraction.ML.Term.fst"
let discrBody = (let _158_458 = (let _158_457 = (let _158_456 = (let _158_455 = (let _158_454 = (let _158_453 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _158_452 = (let _158_451 = (let _158_447 = (let _158_445 = (let _158_444 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_158_444, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_158_445))
in (let _158_446 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_158_447, None, _158_446)))
in (let _158_450 = (let _158_449 = (let _158_448 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _158_448))
in (_158_449)::[])
in (_158_451)::_158_450))
in (_158_453, _158_452)))
in FStar_Extraction_ML_Syntax.MLE_Match (_158_454))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _158_455))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _158_456))
in FStar_Extraction_ML_Syntax.MLE_Fun (_158_457))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _158_458))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




