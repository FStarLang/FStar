
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
let predecessor : level_t  ->  level_t = (fun _72_1 -> (match (_72_1) with
| Term_level -> begin
(FStar_All.failwith "Impossible")
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))

# 119 "FStar.Extraction.ML.Term.fst"
let rec level : FStar_Syntax_Syntax.term  ->  level_t = (fun t -> (match ((let _156_66 = (FStar_Syntax_Subst.compress t)
in _156_66.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_constant (_72_64) -> begin
Term_level
end
| (FStar_Syntax_Syntax.Tm_bvar (x)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
(let _156_67 = (level x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_left predecessor _156_67))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _156_68 = (level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _156_68))
end
| FStar_Syntax_Syntax.Tm_ascribed (_72_72, t, _72_75) -> begin
(let _156_69 = (level t)
in (FStar_All.pipe_left predecessor _156_69))
end
| FStar_Syntax_Syntax.Tm_type (_72_79) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uvar (_72_82, t) -> begin
(let _156_70 = (level t)
in (FStar_All.pipe_left predecessor _156_70))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _72_88) -> begin
(level t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _72_93) -> begin
(let _156_71 = (level t)
in (FStar_All.pipe_left predecessor _156_71))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(level (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_abs (_72_101, _72_103, Some (c)) -> begin
(let _156_72 = (level c.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left predecessor _156_72))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, None) -> begin
(level body)
end
| FStar_Syntax_Syntax.Tm_let (_72_114, body) -> begin
(level body)
end
| FStar_Syntax_Syntax.Tm_match (_72_119, branches) -> begin
(match (branches) with
| (_72_126, _72_128, e)::_72_124 -> begin
(level e)
end
| _72_133 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _72_136) -> begin
(level t)
end
| FStar_Syntax_Syntax.Tm_app (head, _72_141) -> begin
(level head)
end))

# 175 "FStar.Extraction.ML.Term.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((level t)) with
| Term_level -> begin
false
end
| _72_147 -> begin
true
end))

# 179 "FStar.Extraction.ML.Term.fst"
let is_type_binder = (fun x -> (match ((level (Prims.fst x).FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
(FStar_All.failwith "Impossible")
end
| Type_level -> begin
false
end
| Kind_level -> begin
true
end))

# 185 "FStar.Extraction.ML.Term.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_78 = (FStar_Syntax_Subst.compress t)
in _156_78.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _72_172 -> begin
false
end))

# 192 "FStar.Extraction.ML.Term.fst"
let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_81 = (FStar_Syntax_Subst.compress t)
in _156_81.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _72_193 -> (match (_72_193) with
| (te, _72_192) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _72_206 -> begin
false
end))

# 217 "FStar.Extraction.ML.Term.fst"
let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_72_227, fields) -> begin
(FStar_Util.for_all (fun _72_234 -> (match (_72_234) with
| (_72_232, e) -> begin
(is_ml_value e)
end)) fields)
end
| _72_236 -> begin
false
end))

# 230 "FStar.Extraction.ML.Term.fst"
let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (
# 231 "FStar.Extraction.ML.Term.fst"
let rec aux = (fun bs t copt -> (
# 232 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _72_249 -> begin
(
# 236 "FStar.Extraction.ML.Term.fst"
let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))

# 242 "FStar.Extraction.ML.Term.fst"
let unit_binder : FStar_Syntax_Syntax.binder = (let _156_94 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _156_94))

# 246 "FStar.Extraction.ML.Term.fst"
let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (
# 249 "FStar.Extraction.ML.Term.fst"
let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(
# 252 "FStar.Extraction.ML.Term.fst"
let _72_256 = (FStar_List.hd l)
in (match (_72_256) with
| (p1, w1, e1) -> begin
(
# 253 "FStar.Extraction.ML.Term.fst"
let _72_260 = (let _156_97 = (FStar_List.tl l)
in (FStar_List.hd _156_97))
in (match (_72_260) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _72_280 -> begin
def
end)
end))
end))
end))

# 276 "FStar.Extraction.ML.Term.fst"
let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))

# 281 "FStar.Extraction.ML.Term.fst"
let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))

# 286 "FStar.Extraction.ML.Term.fst"
let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (
# 287 "FStar.Extraction.ML.Term.fst"
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

# 295 "FStar.Extraction.ML.Term.fst"
let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (
# 296 "FStar.Extraction.ML.Term.fst"
let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _72_301 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect))))
end)))

# 305 "FStar.Extraction.ML.Term.fst"
let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (let _156_129 = (let _156_128 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (FStar_All.pipe_right _156_128 FStar_Util.left))
in (FStar_All.pipe_right _156_129 Prims.snd)))

# 321 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (
# 322 "FStar.Extraction.ML.Term.fst"
let t = (let _156_143 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (FStar_All.pipe_right _156_143 FStar_Syntax_Subst.compress))
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uvar (_72_320) -> begin
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
# 347 "FStar.Extraction.ML.Term.fst"
let _72_356 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_72_356) with
| (bs, c) -> begin
(
# 348 "FStar.Extraction.ML.Term.fst"
let _72_359 = (binders_as_ml_binders env bs)
in (match (_72_359) with
| (mlbs, env) -> begin
(
# 349 "FStar.Extraction.ML.Term.fst"
let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (
# 350 "FStar.Extraction.ML.Term.fst"
let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (
# 351 "FStar.Extraction.ML.Term.fst"
let _72_372 = (FStar_List.fold_right (fun _72_365 _72_368 -> (match ((_72_365, _72_368)) with
| ((_72_363, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_72_372) with
| (_72_370, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 357 "FStar.Extraction.ML.Term.fst"
let res = (match ((let _156_148 = (FStar_Syntax_Subst.compress head)
in _156_148.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _156_149 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _156_149))
end
| _72_386 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _72_391) -> begin
(
# 373 "FStar.Extraction.ML.Term.fst"
let _72_396 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_72_396) with
| (bs, ty) -> begin
(
# 374 "FStar.Extraction.ML.Term.fst"
let _72_399 = (binders_as_ml_binders env bs)
in (match (_72_399) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _72_413 -> (match (_72_413) with
| (a, _72_412) -> begin
if (is_type a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (
# 387 "FStar.Extraction.ML.Term.fst"
let _72_419 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_72_419) with
| (formals, t) -> begin
(
# 388 "FStar.Extraction.ML.Term.fst"
let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (
# 389 "FStar.Extraction.ML.Term.fst"
let mlargs = (
# 390 "FStar.Extraction.ML.Term.fst"
let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(
# 392 "FStar.Extraction.ML.Term.fst"
let _72_425 = (FStar_Util.first_N n_args formals)
in (match (_72_425) with
| (_72_423, rest) -> begin
(let _156_156 = (FStar_List.map (fun _72_426 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _156_156))
end))
end else begin
mlargs
end)
in (let _156_158 = (let _156_157 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _156_157))
in FStar_Extraction_ML_Syntax.MLTY_Named (_156_158))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (
# 398 "FStar.Extraction.ML.Term.fst"
let _72_444 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _72_433 b -> (match (_72_433) with
| (ml_bs, env) -> begin
if (is_type_binder b) then begin
(
# 401 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 402 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (
# 403 "FStar.Extraction.ML.Term.fst"
let ml_b = (let _156_163 = (FStar_Extraction_ML_UEnv.btvar_as_mlTermVar b)
in (_156_163, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(
# 406 "FStar.Extraction.ML.Term.fst"
let b = (Prims.fst b)
in (
# 407 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (
# 408 "FStar.Extraction.ML.Term.fst"
let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (
# 409 "FStar.Extraction.ML.Term.fst"
let ml_b = ((b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText, 0), t)
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_72_444) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))

# 425 "FStar.Extraction.ML.Term.fst"
let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (
# 426 "FStar.Extraction.ML.Term.fst"
let rec extract_one_pat = (fun disjunctive_pat imp g p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_72_453) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(
# 432 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (
# 433 "FStar.Extraction.ML.Term.fst"
let when_clause = (let _156_184 = (let _156_183 = (let _156_182 = (let _156_181 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _156_180 = (let _156_179 = (let _156_178 = (let _156_177 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p (FStar_Const.Const_int (c)))
in (FStar_All.pipe_left (fun _156_176 -> FStar_Extraction_ML_Syntax.MLE_Const (_156_176)) _156_177))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _156_178))
in (_156_179)::[])
in (_156_181)::_156_180))
in (FStar_Extraction_ML_Util.prims_op_equality, _156_182))
in FStar_Extraction_ML_Syntax.MLE_App (_156_183))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _156_184))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(let _156_188 = (let _156_187 = (let _156_186 = (let _156_185 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_156_185))
in (_156_186, []))
in Some (_156_187))
in (g, _156_188))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(
# 441 "FStar.Extraction.ML.Term.fst"
let _72_482 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _72_469; FStar_Extraction_ML_Syntax.loc = _72_467}, ttys, _72_475) -> begin
(n, ttys)
end
| _72_479 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_72_482) with
| (d, tys) -> begin
(
# 444 "FStar.Extraction.ML.Term.fst"
let nTyVars = (FStar_List.length (Prims.fst tys))
in (
# 445 "FStar.Extraction.ML.Term.fst"
let _72_486 = (FStar_Util.first_N nTyVars pats)
in (match (_72_486) with
| (tysVarPats, restPats) -> begin
(
# 446 "FStar.Extraction.ML.Term.fst"
let _72_493 = (FStar_Util.fold_map (fun g _72_490 -> (match (_72_490) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat true g p)
end)) g tysVarPats)
in (match (_72_493) with
| (g, tyMLPats) -> begin
(
# 447 "FStar.Extraction.ML.Term.fst"
let _72_500 = (FStar_Util.fold_map (fun g _72_497 -> (match (_72_497) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat false g p)
end)) g restPats)
in (match (_72_500) with
| (g, restMLPats) -> begin
(
# 448 "FStar.Extraction.ML.Term.fst"
let _72_508 = (let _156_194 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _72_2 -> (match (_72_2) with
| Some (x) -> begin
(x)::[]
end
| _72_505 -> begin
[]
end))))
in (FStar_All.pipe_right _156_194 FStar_List.split))
in (match (_72_508) with
| (mlPats, when_clauses) -> begin
(let _156_198 = (let _156_197 = (let _156_196 = (FStar_Extraction_ML_Util.resugar_pat None (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _156_195 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_156_196, _156_195)))
in Some (_156_197))
in (g, _156_198))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 452 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 453 "FStar.Extraction.ML.Term.fst"
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
# 460 "FStar.Extraction.ML.Term.fst"
let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (
# 461 "FStar.Extraction.ML.Term.fst"
let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (g, if imp then begin
None
end else begin
Some ((FStar_Extraction_ML_Syntax.MLP_Var ((x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText, 0)), []))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (_72_520) -> begin
(g, None)
end))
in (
# 467 "FStar.Extraction.ML.Term.fst"
let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _72_533 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 472 "FStar.Extraction.ML.Term.fst"
let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _156_207 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_156_207))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(
# 481 "FStar.Extraction.ML.Term.fst"
let _72_548 = (extract_one_pat true g p)
in (match (_72_548) with
| (g, p) -> begin
(
# 482 "FStar.Extraction.ML.Term.fst"
let ps = (let _156_210 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _156_209 = (extract_one_pat true g x)
in (Prims.snd _156_209)))))
in (p)::_156_210)
in (
# 483 "FStar.Extraction.ML.Term.fst"
let _72_564 = (FStar_All.pipe_right ps (FStar_List.partition (fun _72_3 -> (match (_72_3) with
| (_72_553, _72_557::_72_555) -> begin
true
end
| _72_561 -> begin
false
end))))
in (match (_72_564) with
| (ps_when, rest) -> begin
(
# 484 "FStar.Extraction.ML.Term.fst"
let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _72_567 -> (match (_72_567) with
| (x, whens) -> begin
(let _156_213 = (mk_when_clause whens)
in (x, _156_213))
end))))
in (
# 486 "FStar.Extraction.ML.Term.fst"
let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _156_217 = (let _156_216 = (let _156_215 = (let _156_214 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_156_214))
in (_156_215, None))
in (_156_216)::ps)
in (g, _156_217))
end)
in res))
end)))
end))
end
| _72_573 -> begin
(
# 492 "FStar.Extraction.ML.Term.fst"
let _72_578 = (extract_one_pat false g p)
in (match (_72_578) with
| (g, (p, whens)) -> begin
(
# 493 "FStar.Extraction.ML.Term.fst"
let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))

# 512 "FStar.Extraction.ML.Term.fst"
let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (
# 513 "FStar.Extraction.ML.Term.fst"
let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _72_589, t1) -> begin
(
# 515 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _156_232 = (let _156_231 = (let _156_230 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _156_230))
in (_156_231)::more_args)
in (eta_args _156_232 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_72_595, _72_597) -> begin
((FStar_List.rev more_args), t)
end
| _72_601 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 520 "FStar.Extraction.ML.Term.fst"
let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_72_606, args), Some (FStar_Syntax_Syntax.Record_ctor (_72_611, fields))) -> begin
(
# 523 "FStar.Extraction.ML.Term.fst"
let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (
# 524 "FStar.Extraction.ML.Term.fst"
let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _72_620 -> begin
e
end))
in (
# 528 "FStar.Extraction.ML.Term.fst"
let resugar_and_maybe_eta = (fun qual e -> (
# 529 "FStar.Extraction.ML.Term.fst"
let _72_626 = (eta_args [] residualType)
in (match (_72_626) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _156_241 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _156_241))
end
| _72_629 -> begin
(
# 533 "FStar.Extraction.ML.Term.fst"
let _72_632 = (FStar_List.unzip eargs)
in (match (_72_632) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(
# 536 "FStar.Extraction.ML.Term.fst"
let body = (let _156_243 = (let _156_242 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _156_242))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _156_243))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _72_639 -> begin
(FStar_All.failwith "Impossible")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_72_641, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _72_647; FStar_Extraction_ML_Syntax.loc = _72_645}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(
# 544 "FStar.Extraction.ML.Term.fst"
let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (
# 545 "FStar.Extraction.ML.Term.fst"
let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (
# 546 "FStar.Extraction.ML.Term.fst"
let e = (match (args) with
| [] -> begin
proj
end
| _72_664 -> begin
(let _156_245 = (let _156_244 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_156_244, args))
in FStar_Extraction_ML_Syntax.MLE_App (_156_245))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _156_246 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _156_246))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _156_247 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _156_247))
end
| _72_704 -> begin
mlAppExpr
end)))))

# 562 "FStar.Extraction.ML.Term.fst"
let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (
# 563 "FStar.Extraction.ML.Term.fst"
let _72_710 = (term_as_mlexpr' g t)
in (match (_72_710) with
| (e, tag, ty) -> begin
(erase g e ty tag)
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (
# 568 "FStar.Extraction.ML.Term.fst"
let _72_717 = (check_term_as_mlexpr' g t f ty)
in (match (_72_717) with
| (e, t) -> begin
(
# 569 "FStar.Extraction.ML.Term.fst"
let _72_722 = (erase g e t f)
in (match (_72_722) with
| (r, _72_720, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (
# 573 "FStar.Extraction.ML.Term.fst"
let _72_730 = (term_as_mlexpr g e0)
in (match (_72_730) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _156_270 = (maybe_coerce g e t ty)
in (_156_270, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (
# 579 "FStar.Extraction.ML.Term.fst"
let _72_734 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _156_276 = (let _156_275 = (FStar_Syntax_Print.tag_of_term top)
in (let _156_274 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "now synthesizing term (%s) :  %s \n" _156_275 _156_274)))
in (FStar_Util.print_string _156_276))))
in (
# 580 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 597 "FStar.Extraction.ML.Term.fst"
let _72_770 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_72_770) with
| (ty, _72_769) -> begin
(
# 598 "FStar.Extraction.ML.Term.fst"
let ml_ty = (term_as_mlty g ty)
in (let _156_280 = (let _156_279 = (let _156_278 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _156_277 -> FStar_Extraction_ML_Syntax.MLE_Const (_156_277)) _156_278))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _156_279))
in (_156_280, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_72_779), _72_782) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Util.Inr (x, mltys, _72_787), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _156_281 = (maybe_eta_data_and_project_record g qual t x)
in (_156_281, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _72_796 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(
# 617 "FStar.Extraction.ML.Term.fst"
let _72_804 = (FStar_Syntax_Subst.open_term bs body)
in (match (_72_804) with
| (named_binders, open_body) -> begin
(
# 618 "FStar.Extraction.ML.Term.fst"
let _72_807 = (binders_as_ml_binders g named_binders)
in (match (_72_807) with
| (ml_bs, env) -> begin
(
# 619 "FStar.Extraction.ML.Term.fst"
let ml_bs = (FStar_List.rev ml_bs)
in (
# 620 "FStar.Extraction.ML.Term.fst"
let _72_812 = (term_as_mlexpr env body)
in (match (_72_812) with
| (ml_body, f, t) -> begin
(
# 622 "FStar.Extraction.ML.Term.fst"
let _72_822 = (FStar_List.fold_right (fun _72_816 _72_819 -> (match ((_72_816, _72_819)) with
| ((_72_814, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_72_822) with
| (f, tfun) -> begin
(let _156_284 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_156_284, f, tfun))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 629 "FStar.Extraction.ML.Term.fst"
let rec synth_app = (fun is_data _72_831 _72_834 restArgs -> (match ((_72_831, _72_834)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _72_838) -> begin
(
# 637 "FStar.Extraction.ML.Term.fst"
let _72_849 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _156_293 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _156_293))
end else begin
(FStar_List.fold_left (fun _72_842 _72_845 -> (match ((_72_842, _72_845)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(
# 643 "FStar.Extraction.ML.Term.fst"
let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _156_297 = (let _156_296 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_156_296)::out_args)
in (((x, arg))::lbs, _156_297)))
end
end)) ([], []) mlargs_f)
end
in (match (_72_849) with
| (lbs, mlargs) -> begin
(
# 646 "FStar.Extraction.ML.Term.fst"
let app = (let _156_298 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _156_298))
in (
# 647 "FStar.Extraction.ML.Term.fst"
let l_app = (FStar_List.fold_right (fun _72_853 out -> (match (_72_853) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _72_859)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tunit, f', t)) when (is_type arg) -> begin
if (type_leq g tunit FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _156_302 = (let _156_301 = (FStar_Extraction_ML_Util.join f f')
in (_156_301, t))
in (synth_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _156_302 rest))
end else begin
(FStar_All.failwith "Impossible: ill-typed application")
end
end
| ((e0, _72_871)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(
# 660 "FStar.Extraction.ML.Term.fst"
let _72_883 = (term_as_mlexpr g e0)
in (match (_72_883) with
| (e0, f0, tInferred) -> begin
(
# 661 "FStar.Extraction.ML.Term.fst"
let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _156_304 = (let _156_303 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_156_303, t))
in (synth_app is_data (mlhead, ((e0, f0))::mlargs_f) _156_304 rest)))
end))
end
| _72_886 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(synth_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application top restArgs t)
end)
end)
end))
in if (is_type t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(
# 672 "FStar.Extraction.ML.Term.fst"
let head = (FStar_Syntax_Subst.compress head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 677 "FStar.Extraction.ML.Term.fst"
let _72_910 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _72_902 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_72_910) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(
# 678 "FStar.Extraction.ML.Term.fst"
let has_typ_apps = (match (args) with
| (a, _72_915)::_72_912 -> begin
(is_type a)
end
| _72_919 -> begin
false
end)
in (
# 682 "FStar.Extraction.ML.Term.fst"
let _72_965 = (match (vars) with
| _72_924::_72_922 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _72_927 -> begin
(
# 689 "FStar.Extraction.ML.Term.fst"
let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(
# 691 "FStar.Extraction.ML.Term.fst"
let _72_931 = (FStar_Util.first_N n args)
in (match (_72_931) with
| (prefix, rest) -> begin
(
# 693 "FStar.Extraction.ML.Term.fst"
let prefixAsMLTypes = (FStar_List.map (fun _72_935 -> (match (_72_935) with
| (x, _72_934) -> begin
(term_as_mlty g x)
end)) prefix)
in (
# 695 "FStar.Extraction.ML.Term.fst"
let t = (instantiate (vars, t) prefixAsMLTypes)
in (
# 696 "FStar.Extraction.ML.Term.fst"
let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(
# 698 "FStar.Extraction.ML.Term.fst"
let _72_944 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _72_944.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _72_944.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _72_950; FStar_Extraction_ML_Syntax.loc = _72_948}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((
# 699 "FStar.Extraction.ML.Term.fst"
let _72_957 = head
in {FStar_Extraction_ML_Syntax.expr = _72_957.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _72_957.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _72_960 -> begin
(FStar_All.failwith "Impossible")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_72_965) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _156_306 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_156_306, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _72_968 -> begin
(synth_app qual (head_ml, []) (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _72_970 -> begin
(
# 710 "FStar.Extraction.ML.Term.fst"
let _72_974 = (term_as_mlexpr g head)
in (match (_72_974) with
| (head, f, t) -> begin
(synth_app None (head, []) (f, t) args)
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, t, f) -> begin
(
# 715 "FStar.Extraction.ML.Term.fst"
let t = (term_as_mlty g t)
in (
# 716 "FStar.Extraction.ML.Term.fst"
let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (
# 719 "FStar.Extraction.ML.Term.fst"
let _72_987 = (check_term_as_mlexpr g e0 f t)
in (match (_72_987) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(
# 724 "FStar.Extraction.ML.Term.fst"
let maybe_generalize = (fun _72_1001 -> (match (_72_1001) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _72_999; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 725 "FStar.Extraction.ML.Term.fst"
let f_e = (effect_as_etag g lbeff)
in (
# 726 "FStar.Extraction.ML.Term.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _156_309 = (FStar_List.hd bs)
in (FStar_All.pipe_right _156_309 is_type_binder)) -> begin
(
# 730 "FStar.Extraction.ML.Term.fst"
let _72_1010 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_72_1010) with
| (bs, c) -> begin
(
# 737 "FStar.Extraction.ML.Term.fst"
let _72_1020 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _156_311 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _156_311))
end)
in (match (_72_1020) with
| (tbinders, tbody) -> begin
(
# 742 "FStar.Extraction.ML.Term.fst"
let n_tbinders = (FStar_List.length tbinders)
in (
# 743 "FStar.Extraction.ML.Term.fst"
let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _72_1026) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(
# 747 "FStar.Extraction.ML.Term.fst"
let _72_1031 = (FStar_Util.first_N n_tbinders bs)
in (match (_72_1031) with
| (targs, rest_args) -> begin
(
# 751 "FStar.Extraction.ML.Term.fst"
let expected_t = (
# 752 "FStar.Extraction.ML.Term.fst"
let s = (FStar_List.map2 (fun _72_1035 _72_1039 -> (match ((_72_1035, _72_1039)) with
| ((x, _72_1034), (y, _72_1038)) -> begin
(let _156_315 = (let _156_314 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _156_314))
in FStar_Syntax_Syntax.NT (_156_315))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (
# 755 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _72_1046 -> (match (_72_1046) with
| (a, _72_1045) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (
# 756 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty env expected_t)
in (
# 757 "FStar.Extraction.ML.Term.fst"
let polytype = (let _156_319 = (FStar_All.pipe_right targs (FStar_List.map (fun _72_1052 -> (match (_72_1052) with
| (x, _72_1051) -> begin
(FStar_Extraction_ML_UEnv.btvar_as_mltyvar x)
end))))
in (_156_319, expected_t))
in (
# 758 "FStar.Extraction.ML.Term.fst"
let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _72_1056 -> begin
false
end)
in (
# 761 "FStar.Extraction.ML.Term.fst"
let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (
# 762 "FStar.Extraction.ML.Term.fst"
let body = (match (rest_args) with
| [] -> begin
body
end
| _72_1061 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end
| _72_1064 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _72_1066 -> begin
(
# 793 "FStar.Extraction.ML.Term.fst"
let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (
# 796 "FStar.Extraction.ML.Term.fst"
let check_lb = (fun env _72_1081 -> (match (_72_1081) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(
# 797 "FStar.Extraction.ML.Term.fst"
let env = (FStar_List.fold_left (fun env _72_1086 -> (match (_72_1086) with
| (a, _72_1085) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (
# 798 "FStar.Extraction.ML.Term.fst"
let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (
# 799 "FStar.Extraction.ML.Term.fst"
let _72_1092 = (check_term_as_mlexpr env e f expected_t)
in (match (_72_1092) with
| (e, _72_1091) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (
# 803 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (
# 805 "FStar.Extraction.ML.Term.fst"
let _72_1116 = (FStar_List.fold_right (fun lb _72_1097 -> (match (_72_1097) with
| (env, lbs) -> begin
(
# 806 "FStar.Extraction.ML.Term.fst"
let _72_1110 = lb
in (match (_72_1110) with
| (lbname, _72_1100, (t, (_72_1103, polytype)), add_unit, _72_1109) -> begin
(
# 807 "FStar.Extraction.ML.Term.fst"
let _72_1113 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_72_1113) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_72_1116) with
| (env_body, lbs) -> begin
(
# 810 "FStar.Extraction.ML.Term.fst"
let env_def = if is_rec then begin
env_body
end else begin
g
end
in (
# 812 "FStar.Extraction.ML.Term.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (
# 814 "FStar.Extraction.ML.Term.fst"
let _72_1122 = (term_as_mlexpr env_body e')
in (match (_72_1122) with
| (e', f', t') -> begin
(
# 816 "FStar.Extraction.ML.Term.fst"
let f = (let _156_329 = (let _156_328 = (FStar_List.map Prims.fst lbs)
in (f')::_156_328)
in (FStar_Extraction_ML_Util.join_l _156_329))
in (let _156_335 = (let _156_334 = (let _156_332 = (let _156_331 = (let _156_330 = (FStar_List.map Prims.snd lbs)
in (is_rec, _156_330))
in (_156_331, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_156_332))
in (let _156_333 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _156_334 _156_333)))
in (_156_335, f, t')))
end))))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(
# 821 "FStar.Extraction.ML.Term.fst"
let _72_1131 = (term_as_mlexpr g scrutinee)
in (match (_72_1131) with
| (e, f_e, t_e) -> begin
(
# 822 "FStar.Extraction.ML.Term.fst"
let _72_1135 = (check_pats_for_ite pats)
in (match (_72_1135) with
| (b, then_e, else_e) -> begin
(
# 823 "FStar.Extraction.ML.Term.fst"
let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(
# 827 "FStar.Extraction.ML.Term.fst"
let _72_1147 = (term_as_mlexpr g then_e)
in (match (_72_1147) with
| (then_mle, f_then, t_then) -> begin
(
# 828 "FStar.Extraction.ML.Term.fst"
let _72_1151 = (term_as_mlexpr g else_e)
in (match (_72_1151) with
| (else_mle, f_else, t_else) -> begin
(
# 829 "FStar.Extraction.ML.Term.fst"
let _72_1154 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_72_1154) with
| (t_branch, maybe_lift) -> begin
(let _156_366 = (let _156_364 = (let _156_363 = (let _156_362 = (maybe_lift then_mle t_then)
in (let _156_361 = (let _156_360 = (maybe_lift else_mle t_else)
in Some (_156_360))
in (e, _156_362, _156_361)))
in FStar_Extraction_ML_Syntax.MLE_If (_156_363))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _156_364))
in (let _156_365 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_156_366, _156_365, t_branch)))
end))
end))
end))
end
| _72_1156 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(
# 840 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun _72_1160 -> (match (_72_1160) with
| (pat, when_opt, branch) -> begin
(
# 841 "FStar.Extraction.ML.Term.fst"
let _72_1163 = (extract_pat g pat)
in (match (_72_1163) with
| (env, p) -> begin
(
# 842 "FStar.Extraction.ML.Term.fst"
let _72_1174 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(
# 845 "FStar.Extraction.ML.Term.fst"
let _72_1170 = (term_as_mlexpr env w)
in (match (_72_1170) with
| (w, f_w, t_w) -> begin
(
# 846 "FStar.Extraction.ML.Term.fst"
let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_72_1174) with
| (when_opt, f_when) -> begin
(
# 848 "FStar.Extraction.ML.Term.fst"
let _72_1178 = (term_as_mlexpr env branch)
in (match (_72_1178) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _72_1181 -> (match (_72_1181) with
| (p, wopt) -> begin
(
# 851 "FStar.Extraction.ML.Term.fst"
let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
end))))
end))
end))
end))
end))))
in (match (mlbranches) with
| [] -> begin
(
# 856 "FStar.Extraction.ML.Term.fst"
let _72_1190 = (let _156_370 = (let _156_369 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _156_369))
in (FStar_All.pipe_left FStar_Util.right _156_370))
in (match (_72_1190) with
| (fw, _72_1187, _72_1189) -> begin
(let _156_375 = (let _156_374 = (let _156_373 = (let _156_372 = (let _156_371 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_156_371)::[])
in (fw, _156_372))
in FStar_Extraction_ML_Syntax.MLE_App (_156_373))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _156_374))
in (_156_375, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_72_1193, _72_1195, (_72_1197, f_first, t_first))::rest -> begin
(
# 863 "FStar.Extraction.ML.Term.fst"
let _72_1223 = (FStar_List.fold_left (fun _72_1205 _72_1215 -> (match ((_72_1205, _72_1215)) with
| ((topt, f), (_72_1207, _72_1209, (_72_1211, f_branch, t_branch))) -> begin
(
# 867 "FStar.Extraction.ML.Term.fst"
let f = (FStar_Extraction_ML_Util.join f f_branch)
in (
# 868 "FStar.Extraction.ML.Term.fst"
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
in (match (_72_1223) with
| (topt, f_match) -> begin
(
# 881 "FStar.Extraction.ML.Term.fst"
let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _72_1234 -> (match (_72_1234) with
| (p, (wopt, _72_1227), (b, _72_1231, t)) -> begin
(
# 882 "FStar.Extraction.ML.Term.fst"
let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_72_1237) -> begin
b
end)
in (p, wopt, b))
end))))
in (
# 888 "FStar.Extraction.ML.Term.fst"
let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _156_379 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_156_379, f_match, t_match))))
end))
end))
end)
end))
end))
end))))

# 896 "FStar.Extraction.ML.Term.fst"
let fresh : Prims.string  ->  (Prims.string * Prims.int) = (
# 896 "FStar.Extraction.ML.Term.fst"
let c = (FStar_Util.mk_ref 0)
in (fun x -> (
# 897 "FStar.Extraction.ML.Term.fst"
let _72_1247 = (FStar_Util.incr c)
in (let _156_382 = (FStar_ST.read c)
in (x, _156_382)))))

# 899 "FStar.Extraction.ML.Term.fst"
let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (
# 901 "FStar.Extraction.ML.Term.fst"
let _72_1255 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_72_1255) with
| (_72_1253, fstar_disc_type) -> begin
(
# 902 "FStar.Extraction.ML.Term.fst"
let wildcards = (match (fstar_disc_type.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _72_1258) -> begin
(let _156_392 = (FStar_All.pipe_right binders (FStar_List.filter (fun _72_4 -> (match (_72_4) with
| (_72_1263, Some (FStar_Syntax_Syntax.Implicit (_72_1265))) -> begin
true
end
| _72_1270 -> begin
false
end))))
in (FStar_All.pipe_right _156_392 (FStar_List.map (fun _72_1271 -> (let _156_391 = (fresh "_")
in (_156_391, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _72_1274 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (
# 913 "FStar.Extraction.ML.Term.fst"
let mlid = (fresh "_discr_")
in (
# 914 "FStar.Extraction.ML.Term.fst"
let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 917 "FStar.Extraction.ML.Term.fst"
let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (
# 918 "FStar.Extraction.ML.Term.fst"
let discrBody = (let _156_407 = (let _156_406 = (let _156_405 = (let _156_404 = (let _156_403 = (let _156_402 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _156_401 = (let _156_400 = (let _156_396 = (let _156_394 = (let _156_393 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_156_393, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_156_394))
in (let _156_395 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_156_396, None, _156_395)))
in (let _156_399 = (let _156_398 = (let _156_397 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _156_397))
in (_156_398)::[])
in (_156_400)::_156_399))
in (_156_402, _156_401)))
in FStar_Extraction_ML_Syntax.MLE_Match (_156_403))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _156_404))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _156_405))
in FStar_Extraction_ML_Syntax.MLE_Fun (_156_406))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _156_407))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




