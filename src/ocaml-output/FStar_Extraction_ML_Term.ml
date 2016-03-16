
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
let _72_17 = (let _156_28 = (let _156_27 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _156_27 msg))
in (FStar_All.pipe_left FStar_Util.print_string _156_28))
in (FStar_All.failwith msg)))

# 62 "FStar.Extraction.ML.Term.fst"
let err_uninst = (fun env t _72_23 -> (match (_72_23) with
| (vars, ty) -> begin
(let _156_36 = (let _156_35 = (FStar_Syntax_Print.term_to_string t)
in (let _156_34 = (let _156_32 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _156_32 (FStar_String.concat ", ")))
in (let _156_33 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _156_35 _156_34 _156_33))))
in (fail t.FStar_Syntax_Syntax.pos _156_36))
end))

# 68 "FStar.Extraction.ML.Term.fst"
let err_ill_typed_application = (fun t args ty -> (let _156_44 = (let _156_43 = (FStar_Syntax_Print.term_to_string t)
in (let _156_42 = (let _156_41 = (FStar_All.pipe_right args (FStar_List.map (fun _72_30 -> (match (_72_30) with
| (x, _72_29) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _156_41 (FStar_String.concat " ")))
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _156_43 _156_42)))
in (fail t.FStar_Syntax_Syntax.pos _156_44)))

# 74 "FStar.Extraction.ML.Term.fst"
let err_value_restriction = (fun t -> (fail t.FStar_Syntax_Syntax.pos "Refusing to generalize because of the value restriction"))

# 77 "FStar.Extraction.ML.Term.fst"
let err_unexpected_eff = (fun t f0 f1 -> (let _156_50 = (let _156_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _156_49 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _156_50)))

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
| Some (_72_44, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (
# 92 "FStar.Extraction.ML.Term.fst"
let _72_49 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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
let predecessor = (fun t _72_1 -> (match (_72_1) with
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
in (
# 122 "FStar.Extraction.ML.Term.fst"
let _72_66 = (FStar_Extraction_ML_UEnv.debug env (fun _72_64 -> (let _156_71 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "level %s\n" _156_71))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_72_69) -> begin
(let _156_76 = (let _156_75 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _156_75))
in (FStar_All.failwith _156_76))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_72_73) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _72_81; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_72_78); FStar_Syntax_Syntax.fv_qual = _72_76}) -> begin
(let _156_77 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (level env _156_77))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _156_78 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _156_78))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _156_79 = (level env t)
in (FStar_All.pipe_left predecessor _156_79))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _72_105, _72_107) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_72_111) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _72_115) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _72_120) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _72_134) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_72_138, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_72_143, branches) -> begin
(match (branches) with
| (_72_150, _72_152, e)::_72_148 -> begin
(level env e)
end
| _72_157 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _72_160) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _72_165) -> begin
(level env head)
end)))))

# 188 "FStar.Extraction.ML.Term.fst"
let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _72_172 -> begin
true
end))

# 192 "FStar.Extraction.ML.Term.fst"
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

# 198 "FStar.Extraction.ML.Term.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_88 = (FStar_Syntax_Subst.compress t)
in _156_88.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _72_198 -> begin
false
end))

# 205 "FStar.Extraction.ML.Term.fst"
let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_91 = (FStar_Syntax_Subst.compress t)
in _156_91.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _72_219 -> (match (_72_219) with
| (te, _72_218) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _72_232 -> begin
false
end))

# 230 "FStar.Extraction.ML.Term.fst"
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_72_253, fields) -> begin
(FStar_Util.for_all (fun _72_260 -> (match (_72_260) with
| (_72_258, e) -> begin
(is_ml_value e)
end)) fields)
end
| _72_262 -> begin
false
end))

# 243 "FStar.Extraction.ML.Term.fst"
let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (
# 244 "FStar.Extraction.ML.Term.fst"
let rec aux = (fun bs t copt -> (
# 245 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _72_275 -> begin
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

# 255 "FStar.Extraction.ML.Term.fst"
let unit_binder : FStar_Syntax_Syntax.binder = (let _156_104 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _156_104))

# 259 "FStar.Extraction.ML.Term.fst"
let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (
# 262 "FStar.Extraction.ML.Term.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 265 "FStar.Extraction.ML.Term.fst"
let _72_282 = (FStar_List.hd l)
in (match (_72_282) with
| (p1, w1, e1) -> begin
(
# 266 "FStar.Extraction.ML.Term.fst"
let _72_286 = (let _156_107 = (FStar_List.tl l)
in (FStar_List.hd _156_107))
in (match (_72_286) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _72_306 -> begin
def
end)
end))
end))
end))

# 289 "FStar.Extraction.ML.Term.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 294 "FStar.Extraction.ML.Term.fst"
let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))

# 299 "FStar.Extraction.ML.Term.fst"
let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (
# 300 "FStar.Extraction.ML.Term.fst"
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

# 308 "FStar.Extraction.ML.Term.fst"
let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (
# 309 "FStar.Extraction.ML.Term.fst"
let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _72_327 -> begin
(
# 313 "FStar.Extraction.ML.Term.fst"
let _72_329 = (FStar_Extraction_ML_UEnv.debug g (fun _72_328 -> (match (()) with
| () -> begin
(let _156_137 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _156_136 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _156_135 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _156_137 _156_136 _156_135))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))

# 322 "FStar.Extraction.ML.Term.fst"
let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (let _156_143 = (let _156_142 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (FStar_All.pipe_right _156_142 FStar_Util.left))
in (FStar_All.pipe_right _156_143 Prims.snd)))

# 338 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (
# 339 "FStar.Extraction.ML.Term.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (
# 343 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _156_160 = (let _156_159 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _156_159))
in (FStar_All.failwith _156_160))
end
| FStar_Syntax_Syntax.Tm_uvar (_72_350) -> begin
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
# 366 "FStar.Extraction.ML.Term.fst"
let _72_386 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_72_386) with
| (bs, c) -> begin
(
# 367 "FStar.Extraction.ML.Term.fst"
let _72_389 = (binders_as_ml_binders env bs)
in (match (_72_389) with
| (mlbs, env) -> begin
(
# 368 "FStar.Extraction.ML.Term.fst"
let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (
# 369 "FStar.Extraction.ML.Term.fst"
let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (
# 370 "FStar.Extraction.ML.Term.fst"
let _72_402 = (FStar_List.fold_right (fun _72_395 _72_398 -> (match ((_72_395, _72_398)) with
| ((_72_393, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_72_402) with
| (_72_400, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 376 "FStar.Extraction.ML.Term.fst"
let res = (match ((let _156_163 = (FStar_Syntax_Subst.compress head)
in _156_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _156_164 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _156_164))
end
| _72_416 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _72_421) -> begin
(
# 392 "FStar.Extraction.ML.Term.fst"
let _72_426 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_72_426) with
| (bs, ty) -> begin
(
# 393 "FStar.Extraction.ML.Term.fst"
let _72_429 = (binders_as_ml_binders env bs)
in (match (_72_429) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _72_443 -> (match (_72_443) with
| (a, _72_442) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (
# 406 "FStar.Extraction.ML.Term.fst"
let _72_449 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_72_449) with
| (formals, t) -> begin
(
# 407 "FStar.Extraction.ML.Term.fst"
let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (
# 408 "FStar.Extraction.ML.Term.fst"
let mlargs = (
# 409 "FStar.Extraction.ML.Term.fst"
let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(
# 411 "FStar.Extraction.ML.Term.fst"
let _72_455 = (FStar_Util.first_N n_args formals)
in (match (_72_455) with
| (_72_453, rest) -> begin
(let _156_171 = (FStar_List.map (fun _72_456 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _156_171))
end))
end else begin
mlargs
end)
in (let _156_173 = (let _156_172 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _156_172))
in FStar_Extraction_ML_Syntax.MLTY_Named (_156_173))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (
# 417 "FStar.Extraction.ML.Term.fst"
let _72_474 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _72_463 b -> (match (_72_463) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(
# 420 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 421 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 422 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _156_178 = (FStar_Extraction_ML_UEnv.btvar_as_mlTermVar b)
in (_156_178, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(
# 425 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 426 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (
# 427 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (
# 428 "FStar.Extraction.ML.Term.fst"
let ml_b = ((b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText, 0), t)
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_72_474) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))

# 444 "FStar.Extraction.ML.Term.fst"
let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 445 "FStar.Extraction.ML.Term.fst"
let rec extract_one_pat = (fun disjunctive_pat imp g p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_72_483) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 451 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (
# 452 "FStar.Extraction.ML.Term.fst"
let when_clause = (let _156_199 = (let _156_198 = (let _156_197 = (let _156_196 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _156_195 = (let _156_194 = (let _156_193 = (let _156_192 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _156_191 -> FStar_Extraction_ML_Syntax.MLE_Const (_156_191)) _156_192))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _156_193))
in (_156_194)::[])
in (_156_196)::_156_195))
in (FStar_Extraction_ML_Util.prims_op_equality, _156_197))
in FStar_Extraction_ML_Syntax.MLE_App (_156_198))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _156_199))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(let _156_203 = (let _156_202 = (let _156_201 = (let _156_200 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_156_200))
in (_156_201, []))
in Some (_156_202))
in (g, _156_203))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(
# 460 "FStar.Extraction.ML.Term.fst"
let _72_512 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _72_499; FStar_Extraction_ML_Syntax.loc = _72_497}, ttys, _72_505) -> begin
(n, ttys)
end
| _72_509 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_72_512) with
| (d, tys) -> begin
(
# 463 "FStar.Extraction.ML.Term.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 464 "FStar.Extraction.ML.Term.fst"
let _72_516 = (FStar_Util.first_N nTyVars pats)
in (match (_72_516) with
| (tysVarPats, restPats) -> begin
(
# 465 "FStar.Extraction.ML.Term.fst"
let _72_523 = (FStar_Util.fold_map (fun g _72_520 -> (match (_72_520) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat true g p)
end)) g tysVarPats)
in (match (_72_523) with
| (g, tyMLPats) -> begin
(
# 466 "FStar.Extraction.ML.Term.fst"
let _72_530 = (FStar_Util.fold_map (fun g _72_527 -> (match (_72_527) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat false g p)
end)) g restPats)
in (match (_72_530) with
| (g, restMLPats) -> begin
(
# 467 "FStar.Extraction.ML.Term.fst"
let _72_538 = (let _156_209 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _72_2 -> (match (_72_2) with
| Some (x) -> begin
(x)::[]
end
| _72_535 -> begin
[]
end))))
in (FStar_All.pipe_right _156_209 FStar_List.split))
in (match (_72_538) with
| (mlPats, when_clauses) -> begin
(let _156_213 = (let _156_212 = (let _156_211 = (FStar_Extraction_ML_Util.resugar_pat None (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _156_210 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_156_211, _156_210)))
in Some (_156_212))
in (g, _156_213))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 471 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 472 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText, 0)), []))
end)))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 479 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 480 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText, 0)), []))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (_72_550) -> begin
(g, None)
end))
in (
# 486 "FStar.Extraction.ML.Term.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _72_563 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (
# 491 "FStar.Extraction.ML.Term.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _156_222 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_156_222))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(
# 500 "FStar.Extraction.ML.Term.fst"
let _72_578 = (extract_one_pat true g p)
in (match (_72_578) with
| (g, p) -> begin
(
# 501 "FStar.Extraction.ML.Term.fst"
let ps = (let _156_225 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _156_224 = (extract_one_pat true g x)
in (Prims.snd _156_224)))))
in (p)::_156_225)
in (
# 502 "FStar.Extraction.ML.Term.fst"
let _72_594 = (FStar_All.pipe_right ps (FStar_List.partition (fun _72_3 -> (match (_72_3) with
| (_72_583, _72_587::_72_585) -> begin
true
end
| _72_591 -> begin
false
end))))
in (match (_72_594) with
| (ps_when, rest) -> begin
(
# 503 "FStar.Extraction.ML.Term.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _72_597 -> (match (_72_597) with
| (x, whens) -> begin
(let _156_228 = (mk_when_clause whens)
in (x, _156_228))
end))))
in (
# 505 "FStar.Extraction.ML.Term.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _156_232 = (let _156_231 = (let _156_230 = (let _156_229 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_156_229))
in (_156_230, None))
in (_156_231)::ps)
in (g, _156_232))
end)
in res))
end)))
end))
end
| _72_603 -> begin
(
# 511 "FStar.Extraction.ML.Term.fst"
let _72_608 = (extract_one_pat false g p)
in (match (_72_608) with
| (g, (p, whens)) -> begin
(
# 512 "FStar.Extraction.ML.Term.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 531 "FStar.Extraction.ML.Term.fst"
let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 532 "FStar.Extraction.ML.Term.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _72_619, t1) -> begin
(
# 534 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _156_247 = (let _156_246 = (let _156_245 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _156_245))
in (_156_246)::more_args)
in (eta_args _156_247 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_72_625, _72_627) -> begin
((FStar_List.rev more_args), t)
end
| _72_631 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (
# 539 "FStar.Extraction.ML.Term.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_72_636, args), Some (FStar_Syntax_Syntax.Record_ctor (_72_641, fields))) -> begin
(
# 542 "FStar.Extraction.ML.Term.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 543 "FStar.Extraction.ML.Term.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _72_650 -> begin
e
end))
in (
# 547 "FStar.Extraction.ML.Term.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 548 "FStar.Extraction.ML.Term.fst"
let _72_656 = (eta_args [] residualType)
in (match (_72_656) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _156_256 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _156_256))
end
| _72_659 -> begin
(
# 552 "FStar.Extraction.ML.Term.fst"
let _72_662 = (FStar_List.unzip eargs)
in (match (_72_662) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 555 "FStar.Extraction.ML.Term.fst"
let body = (let _156_258 = (let _156_257 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _156_257))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _156_258))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _72_669 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_72_671, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _72_677; FStar_Extraction_ML_Syntax.loc = _72_675}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(
# 563 "FStar.Extraction.ML.Term.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 564 "FStar.Extraction.ML.Term.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 565 "FStar.Extraction.ML.Term.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _72_694 -> begin
(let _156_260 = (let _156_259 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_156_259, args))
in FStar_Extraction_ML_Syntax.MLE_App (_156_260))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _156_261 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _156_261))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _156_262 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _156_262))
end
| _72_734 -> begin
mlAppExpr
end)))))

# 581 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (
# 582 "FStar.Extraction.ML.Term.fst"
let _72_740 = (term_as_mlexpr' g t)
in (match (_72_740) with
| (e, tag, ty) -> begin
(erase g e ty tag)
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (
# 587 "FStar.Extraction.ML.Term.fst"
let _72_747 = (check_term_as_mlexpr' g t f ty)
in (match (_72_747) with
| (e, t) -> begin
(
# 588 "FStar.Extraction.ML.Term.fst"
let _72_752 = (erase g e t f)
in (match (_72_752) with
| (r, _72_750, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (
# 592 "FStar.Extraction.ML.Term.fst"
let _72_760 = (term_as_mlexpr g e0)
in (match (_72_760) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _156_285 = (maybe_coerce g e t ty)
in (_156_285, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (
# 598 "FStar.Extraction.ML.Term.fst"
let _72_764 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _156_291 = (let _156_290 = (FStar_Syntax_Print.tag_of_term top)
in (let _156_289 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _156_290 _156_289)))
in (FStar_Util.print_string _156_291))))
in (
# 599 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _156_293 = (let _156_292 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _156_292))
in (FStar_All.failwith _156_293))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 616 "FStar.Extraction.ML.Term.fst"
let _72_800 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_72_800) with
| (ty, _72_799) -> begin
(
# 617 "FStar.Extraction.ML.Term.fst"
let ml_ty = (term_as_mlty g ty)
in (let _156_297 = (let _156_296 = (let _156_295 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _156_294 -> FStar_Extraction_ML_Syntax.MLE_Const (_156_294)) _156_295))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _156_296))
in (_156_297, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_72_809), _72_812) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _72_817), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _156_298 = (maybe_eta_data_and_project_record g qual t x)
in (_156_298, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _72_826 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(
# 637 "FStar.Extraction.ML.Term.fst"
let _72_834 = (FStar_Syntax_Subst.open_term bs body)
in (match (_72_834) with
| (bs, body) -> begin
(
# 638 "FStar.Extraction.ML.Term.fst"
let _72_837 = (binders_as_ml_binders g bs)
in (match (_72_837) with
| (ml_bs, env) -> begin
(
# 639 "FStar.Extraction.ML.Term.fst"
let _72_841 = (term_as_mlexpr env body)
in (match (_72_841) with
| (ml_body, f, t) -> begin
(
# 640 "FStar.Extraction.ML.Term.fst"
let _72_851 = (FStar_List.fold_right (fun _72_845 _72_848 -> (match ((_72_845, _72_848)) with
| ((_72_843, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_72_851) with
| (f, tfun) -> begin
(let _156_301 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_156_301, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 646 "FStar.Extraction.ML.Term.fst"
let rec extract_app = (fun is_data _72_860 _72_863 restArgs -> (match ((_72_860, _72_863)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _72_867) -> begin
(
# 654 "FStar.Extraction.ML.Term.fst"
let _72_878 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _156_310 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _156_310))
end else begin
(FStar_List.fold_left (fun _72_871 _72_874 -> (match ((_72_871, _72_874)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 660 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _156_314 = (let _156_313 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_156_313)::out_args)
in (((x, arg))::lbs, _156_314)))
end
end)) ([], []) mlargs_f)
end
in (match (_72_878) with
| (lbs, mlargs) -> begin
(
# 663 "FStar.Extraction.ML.Term.fst"
let app = (let _156_315 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _156_315))
in (
# 664 "FStar.Extraction.ML.Term.fst"
let l_app = (FStar_List.fold_right (fun _72_882 out -> (match (_72_882) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _72_888)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _156_319 = (let _156_318 = (FStar_Extraction_ML_Util.join f f')
in (_156_318, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _156_319 rest))
end else begin
(let _156_324 = (let _156_323 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _156_322 = (FStar_Syntax_Print.term_to_string arg)
in (let _156_321 = (FStar_Syntax_Print.tag_of_term arg)
in (let _156_320 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _156_323 _156_322 _156_321 _156_320)))))
in (FStar_All.failwith _156_324))
end
end
| ((e0, _72_900)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 681 "FStar.Extraction.ML.Term.fst"
let _72_912 = (term_as_mlexpr g e0)
in (match (_72_912) with
| (e0, f0, tInferred) -> begin
(
# 682 "FStar.Extraction.ML.Term.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _156_326 = (let _156_325 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_156_325, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _156_326 rest)))
end))
end
| _72_915 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application top restArgs t)
end)
end)
end))
in if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(
# 693 "FStar.Extraction.ML.Term.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 698 "FStar.Extraction.ML.Term.fst"
let _72_939 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _72_931 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_72_939) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 699 "FStar.Extraction.ML.Term.fst"
let has_typ_apps = (match (args) with
| (a, _72_944)::_72_941 -> begin
(is_type g a)
end
| _72_948 -> begin
false
end)
in (
# 703 "FStar.Extraction.ML.Term.fst"
let _72_994 = (match (vars) with
| _72_953::_72_951 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _72_956 -> begin
(
# 710 "FStar.Extraction.ML.Term.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 712 "FStar.Extraction.ML.Term.fst"
let _72_960 = (FStar_Util.first_N n args)
in (match (_72_960) with
| (prefix, rest) -> begin
(
# 714 "FStar.Extraction.ML.Term.fst"
let prefixAsMLTypes = (FStar_List.map (fun _72_964 -> (match (_72_964) with
| (x, _72_963) -> begin
(term_as_mlty g x)
end)) prefix)
in (
# 716 "FStar.Extraction.ML.Term.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 717 "FStar.Extraction.ML.Term.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 719 "FStar.Extraction.ML.Term.fst"
let _72_973 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _72_973.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _72_973.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _72_979; FStar_Extraction_ML_Syntax.loc = _72_977}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 720 "FStar.Extraction.ML.Term.fst"
let _72_986 = head
in {FStar_Extraction_ML_Syntax.expr = _72_986.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _72_986.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _72_989 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_72_994) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _156_328 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_156_328, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _72_997 -> begin
(extract_app qual (head_ml, []) (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _72_999 -> begin
(
# 731 "FStar.Extraction.ML.Term.fst"
let _72_1003 = (term_as_mlexpr g head)
in (match (_72_1003) with
| (head, f, t) -> begin
(extract_app None (head, []) (f, t) args)
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, t, f) -> begin
(
# 736 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty g t)
in (
# 737 "FStar.Extraction.ML.Term.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (
# 740 "FStar.Extraction.ML.Term.fst"
let _72_1016 = (check_term_as_mlexpr g e0 f t)
in (match (_72_1016) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(
# 744 "FStar.Extraction.ML.Term.fst"
let _72_1031 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(
# 749 "FStar.Extraction.ML.Term.fst"
let lb = (FStar_List.hd lbs)
in (
# 750 "FStar.Extraction.ML.Term.fst"
let x = (let _156_329 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _156_329))
in (
# 751 "FStar.Extraction.ML.Term.fst"
let lb = (
# 751 "FStar.Extraction.ML.Term.fst"
let _72_1025 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _72_1025.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _72_1025.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _72_1025.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _72_1025.FStar_Syntax_Syntax.lbdef})
in (
# 752 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_72_1031) with
| (lbs, e') -> begin
(
# 755 "FStar.Extraction.ML.Term.fst"
let maybe_generalize = (fun _72_1039 -> (match (_72_1039) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _72_1037; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 756 "FStar.Extraction.ML.Term.fst"
let f_e = (effect_as_etag g lbeff)
in (
# 757 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _156_332 = (FStar_List.hd bs)
in (FStar_All.pipe_right _156_332 (is_type_binder g))) -> begin
(
# 761 "FStar.Extraction.ML.Term.fst"
let _72_1048 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_72_1048) with
| (bs, c) -> begin
(
# 768 "FStar.Extraction.ML.Term.fst"
let _72_1058 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _156_334 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _156_334))
end)
in (match (_72_1058) with
| (tbinders, tbody) -> begin
(
# 773 "FStar.Extraction.ML.Term.fst"
let n_tbinders = (FStar_List.length tbinders)
in (
# 774 "FStar.Extraction.ML.Term.fst"
let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _72_1064) -> begin
(
# 777 "FStar.Extraction.ML.Term.fst"
let _72_1069 = (FStar_Syntax_Subst.open_term bs body)
in (match (_72_1069) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(
# 779 "FStar.Extraction.ML.Term.fst"
let _72_1072 = (FStar_Util.first_N n_tbinders bs)
in (match (_72_1072) with
| (targs, rest_args) -> begin
(
# 783 "FStar.Extraction.ML.Term.fst"
let expected_t = (
# 784 "FStar.Extraction.ML.Term.fst"
let s = (FStar_List.map2 (fun _72_1076 _72_1080 -> (match ((_72_1076, _72_1080)) with
| ((x, _72_1075), (y, _72_1079)) -> begin
(let _156_338 = (let _156_337 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _156_337))
in FStar_Syntax_Syntax.NT (_156_338))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (
# 787 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _72_1087 -> (match (_72_1087) with
| (a, _72_1086) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (
# 788 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty env expected_t)
in (
# 789 "FStar.Extraction.ML.Term.fst"
let polytype = (let _156_342 = (FStar_All.pipe_right targs (FStar_List.map (fun _72_1093 -> (match (_72_1093) with
| (x, _72_1092) -> begin
(FStar_Extraction_ML_UEnv.btvar_as_mltyvar x)
end))))
in (_156_342, expected_t))
in (
# 790 "FStar.Extraction.ML.Term.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _72_1097 -> begin
false
end)
in (
# 793 "FStar.Extraction.ML.Term.fst"
let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (
# 794 "FStar.Extraction.ML.Term.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _72_1102 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| _72_1105 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _72_1107 -> begin
(
# 825 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 828 "FStar.Extraction.ML.Term.fst"
let check_lb = (fun env _72_1122 -> (match (_72_1122) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 829 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _72_1127 -> (match (_72_1127) with
| (a, _72_1126) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (
# 830 "FStar.Extraction.ML.Term.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 831 "FStar.Extraction.ML.Term.fst"
let _72_1133 = (check_term_as_mlexpr env e f expected_t)
in (match (_72_1133) with
| (e, _72_1132) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (
# 835 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 837 "FStar.Extraction.ML.Term.fst"
let _72_1157 = (FStar_List.fold_right (fun lb _72_1138 -> (match (_72_1138) with
| (env, lbs) -> begin
(
# 838 "FStar.Extraction.ML.Term.fst"
let _72_1151 = lb
in (match (_72_1151) with
| (lbname, _72_1141, (t, (_72_1144, polytype)), add_unit, _72_1150) -> begin
(
# 839 "FStar.Extraction.ML.Term.fst"
let _72_1154 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_72_1154) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_72_1157) with
| (env_body, lbs) -> begin
(
# 842 "FStar.Extraction.ML.Term.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 844 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 846 "FStar.Extraction.ML.Term.fst"
let _72_1163 = (term_as_mlexpr env_body e')
in (match (_72_1163) with
| (e', f', t') -> begin
(
# 848 "FStar.Extraction.ML.Term.fst"
let f = (let _156_352 = (let _156_351 = (FStar_List.map Prims.fst lbs)
in (f')::_156_351)
in (FStar_Extraction_ML_Util.join_l _156_352))
in (let _156_358 = (let _156_357 = (let _156_355 = (let _156_354 = (let _156_353 = (FStar_List.map Prims.snd lbs)
in (is_rec, _156_353))
in (_156_354, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_156_355))
in (let _156_356 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _156_357 _156_356)))
in (_156_358, f, t')))
end))))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(
# 853 "FStar.Extraction.ML.Term.fst"
let _72_1172 = (term_as_mlexpr g scrutinee)
in (match (_72_1172) with
| (e, f_e, t_e) -> begin
(
# 854 "FStar.Extraction.ML.Term.fst"
let _72_1176 = (check_pats_for_ite pats)
in (match (_72_1176) with
| (b, then_e, else_e) -> begin
(
# 855 "FStar.Extraction.ML.Term.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 859 "FStar.Extraction.ML.Term.fst"
let _72_1188 = (term_as_mlexpr g then_e)
in (match (_72_1188) with
| (then_mle, f_then, t_then) -> begin
(
# 860 "FStar.Extraction.ML.Term.fst"
let _72_1192 = (term_as_mlexpr g else_e)
in (match (_72_1192) with
| (else_mle, f_else, t_else) -> begin
(
# 861 "FStar.Extraction.ML.Term.fst"
let _72_1195 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_72_1195) with
| (t_branch, maybe_lift) -> begin
(let _156_389 = (let _156_387 = (let _156_386 = (let _156_385 = (maybe_lift then_mle t_then)
in (let _156_384 = (let _156_383 = (maybe_lift else_mle t_else)
in Some (_156_383))
in (e, _156_385, _156_384)))
in FStar_Extraction_ML_Syntax.MLE_If (_156_386))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _156_387))
in (let _156_388 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_156_389, _156_388, t_branch)))
end))
end))
end))
end
| _72_1197 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 872 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (
# 873 "FStar.Extraction.ML.Term.fst"
let _72_1202 = (FStar_Syntax_Subst.open_branch br)
in (match (_72_1202) with
| (pat, when_opt, branch) -> begin
(
# 874 "FStar.Extraction.ML.Term.fst"
let _72_1205 = (extract_pat g pat)
in (match (_72_1205) with
| (env, p) -> begin
(
# 875 "FStar.Extraction.ML.Term.fst"
let _72_1216 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 878 "FStar.Extraction.ML.Term.fst"
let _72_1212 = (term_as_mlexpr env w)
in (match (_72_1212) with
| (w, f_w, t_w) -> begin
(
# 879 "FStar.Extraction.ML.Term.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_72_1216) with
| (when_opt, f_when) -> begin
(
# 881 "FStar.Extraction.ML.Term.fst"
let _72_1220 = (term_as_mlexpr env branch)
in (match (_72_1220) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _72_1223 -> (match (_72_1223) with
| (p, wopt) -> begin
(
# 884 "FStar.Extraction.ML.Term.fst"
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
# 889 "FStar.Extraction.ML.Term.fst"
let _72_1232 = (let _156_393 = (let _156_392 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _156_392))
in (FStar_All.pipe_left FStar_Util.right _156_393))
in (match (_72_1232) with
| (fw, _72_1229, _72_1231) -> begin
(let _156_398 = (let _156_397 = (let _156_396 = (let _156_395 = (let _156_394 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_156_394)::[])
in (fw, _156_395))
in FStar_Extraction_ML_Syntax.MLE_App (_156_396))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _156_397))
in (_156_398, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_72_1235, _72_1237, (_72_1239, f_first, t_first))::rest -> begin
(
# 896 "FStar.Extraction.ML.Term.fst"
let _72_1265 = (FStar_List.fold_left (fun _72_1247 _72_1257 -> (match ((_72_1247, _72_1257)) with
| ((topt, f), (_72_1249, _72_1251, (_72_1253, f_branch, t_branch))) -> begin
(
# 900 "FStar.Extraction.ML.Term.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 901 "FStar.Extraction.ML.Term.fst"
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
in (match (_72_1265) with
| (topt, f_match) -> begin
(
# 914 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _72_1276 -> (match (_72_1276) with
| (p, (wopt, _72_1269), (b, _72_1273, t)) -> begin
(
# 915 "FStar.Extraction.ML.Term.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_72_1279) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 921 "FStar.Extraction.ML.Term.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _156_402 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_156_402, f_match, t_match))))
end))
end))
end)
end))
end))
end))))

# 929 "FStar.Extraction.ML.Term.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 929 "FStar.Extraction.ML.Term.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 930 "FStar.Extraction.ML.Term.fst"
let _72_1289 = (FStar_Util.incr c)
in (let _156_405 = (FStar_ST.read c)
in (x, _156_405)))))

# 932 "FStar.Extraction.ML.Term.fst"
let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 934 "FStar.Extraction.ML.Term.fst"
let _72_1297 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_72_1297) with
| (_72_1295, fstar_disc_type) -> begin
(
# 935 "FStar.Extraction.ML.Term.fst"
let wildcards = (match ((let _156_412 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _156_412.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _72_1300) -> begin
(let _156_416 = (FStar_All.pipe_right binders (FStar_List.filter (fun _72_4 -> (match (_72_4) with
| (_72_1305, Some (FStar_Syntax_Syntax.Implicit (_72_1307))) -> begin
true
end
| _72_1312 -> begin
false
end))))
in (FStar_All.pipe_right _156_416 (FStar_List.map (fun _72_1313 -> (let _156_415 = (fresh "_")
in (_156_415, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _72_1316 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 946 "FStar.Extraction.ML.Term.fst"
let mlid = (fresh "_discr_")
in (
# 947 "FStar.Extraction.ML.Term.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 950 "FStar.Extraction.ML.Term.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 951 "FStar.Extraction.ML.Term.fst"
let discrBody = (let _156_431 = (let _156_430 = (let _156_429 = (let _156_428 = (let _156_427 = (let _156_426 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _156_425 = (let _156_424 = (let _156_420 = (let _156_418 = (let _156_417 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_156_417, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_156_418))
in (let _156_419 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_156_420, None, _156_419)))
in (let _156_423 = (let _156_422 = (let _156_421 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _156_421))
in (_156_422)::[])
in (_156_424)::_156_423))
in (_156_426, _156_425)))
in FStar_Extraction_ML_Syntax.MLE_Match (_156_427))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _156_428))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _156_429))
in FStar_Extraction_ML_Syntax.MLE_Fun (_156_430))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _156_431))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




