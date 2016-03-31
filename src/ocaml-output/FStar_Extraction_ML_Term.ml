
open Prims

let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let fail = (fun r msg -> (

let _77_17 = (let _166_28 = (let _166_27 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _166_27 msg))
in (FStar_All.pipe_left FStar_Util.print_string _166_28))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _77_23 -> (match (_77_23) with
| (vars, ty) -> begin
(let _166_36 = (let _166_35 = (FStar_Syntax_Print.term_to_string t)
in (let _166_34 = (let _166_32 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _166_32 (FStar_String.concat ", ")))
in (let _166_33 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _166_35 _166_34 _166_33))))
in (fail t.FStar_Syntax_Syntax.pos _166_36))
end))


let err_ill_typed_application = (fun t args ty -> (let _166_44 = (let _166_43 = (FStar_Syntax_Print.term_to_string t)
in (let _166_42 = (let _166_41 = (FStar_All.pipe_right args (FStar_List.map (fun _77_30 -> (match (_77_30) with
| (x, _77_29) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _166_41 (FStar_String.concat " ")))
in (FStar_Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n" _166_43 _166_42)))
in (fail t.FStar_Syntax_Syntax.pos _166_44)))


let err_value_restriction = (fun t -> (fail t.FStar_Syntax_Syntax.pos "Refusing to generalize because of the value restriction"))


let err_unexpected_eff = (fun t f0 f1 -> (let _166_50 = (let _166_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _166_49 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _166_50)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create 20)
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv FStar_Syntax_Syntax.U_zero l)) with
| None -> begin
l
end
| Some (_77_44, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _77_49 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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


let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (

let predecessor = (fun l -> (predecessor t l))
in (

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

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (level env t'))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _166_75 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _166_75))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _166_76 = (level env t)
in (FStar_All.pipe_left predecessor _166_76))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _77_102, _77_104) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_77_108) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _77_112) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _77_117) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_131) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_77_135, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_77_140, branches) -> begin
(match (branches) with
| (_77_147, _77_149, e)::_77_145 -> begin
(level env e)
end
| _77_154 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _77_157) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _77_162) -> begin
(level env head)
end))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _77_169 -> begin
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


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _166_85 = (FStar_Syntax_Subst.compress t)
in _166_85.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _77_195 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _166_88 = (FStar_Syntax_Subst.compress t)
in _166_88.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _77_216 -> (match (_77_216) with
| (te, _77_215) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _77_229 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_77_250, fields) -> begin
(FStar_Util.for_all (fun _77_257 -> (match (_77_257) with
| (_77_255, e) -> begin
(is_ml_value e)
end)) fields)
end
| _77_259 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _77_272 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _166_101 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _166_101))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(

let _77_279 = (FStar_List.hd l)
in (match (_77_279) with
| (p1, w1, e1) -> begin
(

let _77_283 = (let _166_104 = (FStar_List.tl l)
in (FStar_List.hd _166_104))
in (match (_77_283) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _77_303 -> begin
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
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.ml_unit_ty, ty))))
end
end else begin
e
end
in (e, f, ty)))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _77_324 -> begin
(

let _77_326 = (FStar_Extraction_ML_UEnv.debug g (fun _77_325 -> (match (()) with
| () -> begin
(let _166_134 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _166_133 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _166_132 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _166_134 _166_133 _166_132))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_77_331, t) -> begin
t
end
| _77_336 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _166_155 = (let _166_154 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _166_154))
in (FStar_All.failwith _166_155))
end
| FStar_Syntax_Syntax.Tm_uvar (_77_354) -> begin
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

let _77_390 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_390) with
| (bs, c) -> begin
(

let _77_393 = (binders_as_ml_binders env bs)
in (match (_77_393) with
| (mlbs, env) -> begin
(

let t_ret = (term_as_mlty' env (FStar_Syntax_Util.comp_result c))
in (

let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (

let _77_406 = (FStar_List.fold_right (fun _77_399 _77_402 -> (match ((_77_399, _77_402)) with
| ((_77_397, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_77_406) with
| (_77_404, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _166_158 = (FStar_Syntax_Subst.compress head)
in _166_158.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _166_159 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _166_159))
end
| _77_420 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _77_425) -> begin
(

let _77_430 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_77_430) with
| (bs, ty) -> begin
(

let _77_433 = (binders_as_ml_binders env bs)
in (match (_77_433) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _77_447 -> (match (_77_447) with
| (a, _77_446) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _77_453 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_77_453) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _77_459 = (FStar_Util.first_N n_args formals)
in (match (_77_459) with
| (_77_457, rest) -> begin
(let _166_166 = (FStar_List.map (fun _77_460 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _166_166))
end))
end else begin
mlargs
end)
in (let _166_168 = (let _166_167 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _166_167))
in FStar_Extraction_ML_Syntax.MLTY_Named (_166_168))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _77_478 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _77_467 b -> (match (_77_467) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _166_173 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_166_173, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (

let ml_b = (let _166_174 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_166_174, t))
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_77_478) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _77_488 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_77_490, fns)) -> begin
(

let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (

let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _77_498 -> begin
p
end)
end)
end
| _77_500 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list) = (fun g p -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_77_509) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) when (not ((FStar_ST.read FStar_Options.use_native_int))) -> begin
(

let _77_517 = p.FStar_Syntax_Syntax.v
in (match (_77_517) with
| FStar_Syntax_Syntax.Pat_constant (i) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _166_199 = (let _166_198 = (let _166_197 = (let _166_196 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _166_195 = (let _166_194 = (let _166_193 = (let _166_192 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _166_191 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_191)) _166_192))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _166_193))
in (_166_194)::[])
in (_166_196)::_166_195))
in (FStar_Extraction_ML_Util.bigint_equality, _166_197))
in FStar_Extraction_ML_Syntax.MLE_App (_166_198))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_199))
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])))))
end))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(let _166_203 = (let _166_202 = (let _166_201 = (let _166_200 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_166_200))
in (_166_201, []))
in Some (_166_202))
in (g, _166_203))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _77_542 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _77_529; FStar_Extraction_ML_Syntax.loc = _77_527}, ttys, _77_535) -> begin
(n, ttys)
end
| _77_539 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_77_542) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _77_546 = (FStar_Util.first_N nTyVars pats)
in (match (_77_546) with
| (tysVarPats, restPats) -> begin
(

let _77_553 = (FStar_Util.fold_map (fun g _77_550 -> (match (_77_550) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat true g p)
end)) g tysVarPats)
in (match (_77_553) with
| (g, tyMLPats) -> begin
(

let _77_560 = (FStar_Util.fold_map (fun g _77_557 -> (match (_77_557) with
| (p, imp) -> begin
(extract_one_pat disjunctive_pat false g p)
end)) g restPats)
in (match (_77_560) with
| (g, restMLPats) -> begin
(

let _77_568 = (let _166_209 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _77_2 -> (match (_77_2) with
| Some (x) -> begin
(x)::[]
end
| _77_565 -> begin
[]
end))))
in (FStar_All.pipe_right _166_209 FStar_List.split))
in (match (_77_568) with
| (mlPats, when_clauses) -> begin
(let _166_213 = (let _166_212 = (let _166_211 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _166_210 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_166_211, _166_210)))
in Some (_166_212))
in (g, _166_213))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _166_217 = if imp then begin
None
end else begin
(let _166_216 = (let _166_215 = (let _166_214 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_166_214))
in (_166_215, []))
in Some (_166_216))
end
in (g, _166_217))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _166_221 = if imp then begin
None
end else begin
(let _166_220 = (let _166_219 = (let _166_218 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_166_218))
in (_166_219, []))
in Some (_166_220))
end
in (g, _166_221))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_77_580) -> begin
(g, None)
end))
in (

let extract_one_pat = (fun disj g p -> (match ((extract_one_pat disj false g p)) with
| (g, Some (x, v)) -> begin
(g, (x, v))
end
| _77_593 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| hd::tl -> begin
(let _166_230 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_166_230))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj (p::pats) -> begin
(

let _77_608 = (extract_one_pat true g p)
in (match (_77_608) with
| (g, p) -> begin
(

let ps = (let _166_233 = (FStar_All.pipe_right pats (FStar_List.map (fun x -> (let _166_232 = (extract_one_pat true g x)
in (Prims.snd _166_232)))))
in (p)::_166_233)
in (

let _77_624 = (FStar_All.pipe_right ps (FStar_List.partition (fun _77_3 -> (match (_77_3) with
| (_77_613, _77_617::_77_615) -> begin
true
end
| _77_621 -> begin
false
end))))
in (match (_77_624) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _77_627 -> (match (_77_627) with
| (x, whens) -> begin
(let _166_236 = (mk_when_clause whens)
in (x, _166_236))
end))))
in (

let res = (match (rest) with
| [] -> begin
(g, ps)
end
| rest -> begin
(let _166_240 = (let _166_239 = (let _166_238 = (let _166_237 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_166_237))
in (_166_238, None))
in (_166_239)::ps)
in (g, _166_240))
end)
in res))
end)))
end))
end
| _77_633 -> begin
(

let _77_638 = (extract_one_pat false g p)
in (match (_77_638) with
| (g, (p, whens)) -> begin
(

let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[]))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _77_649, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _166_255 = (let _166_254 = (let _166_253 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _166_253))
in (_166_254)::more_args)
in (eta_args _166_255 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_77_655, _77_657) -> begin
((FStar_List.rev more_args), t)
end
| _77_661 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_77_666, args), Some (FStar_Syntax_Syntax.Record_ctor (_77_671, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _77_680 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _77_686 = (eta_args [] residualType)
in (match (_77_686) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _166_264 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _166_264))
end
| _77_689 -> begin
(

let _77_692 = (FStar_List.unzip eargs)
in (match (_77_692) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _166_266 = (let _166_265 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _166_265))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _166_266))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _77_699 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_77_701, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _77_707; FStar_Extraction_ML_Syntax.loc = _77_705}, mle::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _77_724 -> begin
(let _166_268 = (let _166_267 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_166_267, args))
in FStar_Extraction_ML_Syntax.MLE_App (_166_268))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _166_269 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_269))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _166_270 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _166_270))
end
| _77_764 -> begin
mlAppExpr
end)))))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _77_770 = (term_as_mlexpr' g t)
in (match (_77_770) with
| (e, tag, ty) -> begin
(erase g e ty tag)
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _77_777 = (check_term_as_mlexpr' g t f ty)
in (match (_77_777) with
| (e, t) -> begin
(

let _77_782 = (erase g e t f)
in (match (_77_782) with
| (r, _77_780, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _77_790 = (term_as_mlexpr g e0)
in (match (_77_790) with
| (e, tag, t) -> begin
if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _166_293 = (maybe_coerce g e t ty)
in (_166_293, ty))
end else begin
(err_unexpected_eff e0 f tag)
end
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _77_794 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _166_299 = (let _166_298 = (FStar_Syntax_Print.tag_of_term top)
in (let _166_297 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _166_298 _166_297)))
in (FStar_Util.print_string _166_299))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _166_301 = (let _166_300 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _166_300))
in (FStar_All.failwith _166_301))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _77_830 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_77_830) with
| (ty, _77_829) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _166_305 = (let _166_304 = (let _166_303 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _166_302 -> FStar_Extraction_ML_Syntax.MLE_Const (_166_302)) _166_303))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _166_304))
in (_166_305, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_77_839), _77_842) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _77_847), qual) -> begin
(match (mltys) with
| ([], t) -> begin
(let _166_306 = (maybe_eta_data_and_project_record g qual t x)
in (_166_306, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _77_856 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _77_864 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_864) with
| (bs, body) -> begin
(

let _77_867 = (binders_as_ml_binders g bs)
in (match (_77_867) with
| (ml_bs, env) -> begin
(

let _77_871 = (term_as_mlexpr env body)
in (match (_77_871) with
| (ml_body, f, t) -> begin
(

let _77_881 = (FStar_List.fold_right (fun _77_875 _77_878 -> (match ((_77_875, _77_878)) with
| ((_77_873, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_77_881) with
| (f, tfun) -> begin
(let _166_309 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_166_309, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_77_887) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _77_891 -> begin
(

let rec extract_app = (fun is_data _77_896 _77_899 restArgs -> (match ((_77_896, _77_899)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _77_903) -> begin
(

let _77_914 = if ((FStar_Syntax_Util.is_primop head) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
(let _166_318 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _166_318))
end else begin
(FStar_List.fold_left (fun _77_907 _77_910 -> (match ((_77_907, _77_910)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _166_322 = (let _166_321 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_166_321)::out_args)
in (((x, arg))::lbs, _166_322)))
end
end)) ([], []) mlargs_f)
end
in (match (_77_914) with
| (lbs, mlargs) -> begin
(

let app = (let _166_323 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _166_323))
in (

let l_app = (FStar_List.fold_right (fun _77_918 out -> (match (_77_918) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Let (((false, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]), out))))
end)) lbs app)
in (l_app, f, t)))
end))
end
| ((arg, _77_924)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _166_327 = (let _166_326 = (FStar_Extraction_ML_Util.join f f')
in (_166_326, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _166_327 rest))
end else begin
(let _166_332 = (let _166_331 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _166_330 = (FStar_Syntax_Print.term_to_string arg)
in (let _166_329 = (FStar_Syntax_Print.tag_of_term arg)
in (let _166_328 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _166_331 _166_330 _166_329 _166_328)))))
in (FStar_All.failwith _166_332))
end
end
| ((e0, _77_936)::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let _77_948 = (term_as_mlexpr g e0)
in (match (_77_948) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _166_334 = (let _166_333 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_166_333, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _166_334 rest)))
end))
end
| _77_951 -> begin
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

let extract_app_maybe_projector = (fun is_data mlhead _77_960 args -> (match (_77_960) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_77_963)) -> begin
(

let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| ((_77_972, Some (FStar_Syntax_Syntax.Implicit (_77_974)))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_77_980, f', t)) -> begin
(let _166_349 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _166_349 t))
end
| _77_987 -> begin
(args, f, t)
end))
in (

let _77_991 = (remove_implicits args f t)
in (match (_77_991) with
| (args, f, t) -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)))
end
| _77_993 -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)
end))
in if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let _77_1014 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _77_1006 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_77_1014) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| (a, _77_1019)::_77_1016 -> begin
(is_type g a)
end
| _77_1023 -> begin
false
end)
in (

let _77_1069 = (match (vars) with
| _77_1028::_77_1026 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _77_1031 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _77_1035 = (FStar_Util.first_N n args)
in (match (_77_1035) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _77_1039 -> (match (_77_1039) with
| (x, _77_1038) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate (vars, t) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _77_1048 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _77_1048.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _77_1048.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _77_1054; FStar_Extraction_ML_Syntax.loc = _77_1052}::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((

let _77_1061 = head
in {FStar_Extraction_ML_Syntax.expr = _77_1061.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _77_1061.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _77_1064 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_77_1069) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _166_351 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_166_351, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _77_1072 -> begin
(extract_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _77_1074 -> begin
(

let _77_1078 = (term_as_mlexpr g head)
in (match (_77_1078) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head (f, t) args)
end))
end))
end))
end)
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

let _77_1095 = (check_term_as_mlexpr g e0 f t)
in (match (_77_1095) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let _77_1110 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _166_352 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _166_352))
in (

let lb = (

let _77_1104 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _77_1104.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _77_1104.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _77_1104.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _77_1104.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_77_1110) with
| (lbs, e') -> begin
(

let maybe_generalize = (fun _77_1118 -> (match (_77_1118) with
| {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _77_1116; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _166_355 = (FStar_List.hd bs)
in (FStar_All.pipe_right _166_355 (is_type_binder g))) -> begin
(

let _77_1127 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_1127) with
| (bs, c) -> begin
(

let _77_1137 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _166_357 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _166_357))
end)
in (match (_77_1137) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_1143) -> begin
(

let _77_1148 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_1148) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _77_1151 = (FStar_Util.first_N n_tbinders bs)
in (match (_77_1151) with
| (targs, rest_args) -> begin
(

let expected_t = (

let s = (FStar_List.map2 (fun _77_1155 _77_1159 -> (match ((_77_1155, _77_1159)) with
| ((x, _77_1154), (y, _77_1158)) -> begin
(let _166_361 = (let _166_360 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _166_360))
in FStar_Syntax_Syntax.NT (_166_361))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _77_1166 -> (match (_77_1166) with
| (a, _77_1165) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_t)
in (

let polytype = (let _166_365 = (FStar_All.pipe_right targs (FStar_List.map (fun _77_1172 -> (match (_77_1172) with
| (x, _77_1171) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_166_365, expected_t))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _77_1176 -> begin
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
| _77_1181 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| _77_1184 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _77_1186 -> begin
(

let expected_t = (term_as_mlty g t)
in (lbname, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (

let check_lb = (fun env _77_1201 -> (match (_77_1201) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _77_1206 -> (match (_77_1206) with
| (a, _77_1205) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (

let _77_1212 = (check_term_as_mlexpr env e f expected_t)
in (match (_77_1212) with
| (e, _77_1211) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _77_1236 = (FStar_List.fold_right (fun lb _77_1217 -> (match (_77_1217) with
| (env, lbs) -> begin
(

let _77_1230 = lb
in (match (_77_1230) with
| (lbname, _77_1220, (t, (_77_1223, polytype)), add_unit, _77_1229) -> begin
(

let _77_1233 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_77_1233) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_77_1236) with
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

let _77_1242 = (term_as_mlexpr env_body e')
in (match (_77_1242) with
| (e', f', t') -> begin
(

let f = (let _166_375 = (let _166_374 = (FStar_List.map Prims.fst lbs)
in (f')::_166_374)
in (FStar_Extraction_ML_Util.join_l _166_375))
in (let _166_381 = (let _166_380 = (let _166_378 = (let _166_377 = (let _166_376 = (FStar_List.map Prims.snd lbs)
in (is_rec, _166_376))
in (_166_377, e'))
in FStar_Extraction_ML_Syntax.MLE_Let (_166_378))
in (let _166_379 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _166_380 _166_379)))
in (_166_381, f, t')))
end))))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _77_1251 = (term_as_mlexpr g scrutinee)
in (match (_77_1251) with
| (e, f_e, t_e) -> begin
(

let _77_1255 = (check_pats_for_ite pats)
in (match (_77_1255) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(

let _77_1267 = (term_as_mlexpr g then_e)
in (match (_77_1267) with
| (then_mle, f_then, t_then) -> begin
(

let _77_1271 = (term_as_mlexpr g else_e)
in (match (_77_1271) with
| (else_mle, f_else, t_else) -> begin
(

let _77_1274 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_77_1274) with
| (t_branch, maybe_lift) -> begin
(let _166_412 = (let _166_410 = (let _166_409 = (let _166_408 = (maybe_lift then_mle t_then)
in (let _166_407 = (let _166_406 = (maybe_lift else_mle t_else)
in Some (_166_406))
in (e, _166_408, _166_407)))
in FStar_Extraction_ML_Syntax.MLE_If (_166_409))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _166_410))
in (let _166_411 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_166_412, _166_411, t_branch)))
end))
end))
end))
end
| _77_1276 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let mlbranches = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let _77_1281 = (FStar_Syntax_Subst.open_branch br)
in (match (_77_1281) with
| (pat, when_opt, branch) -> begin
(

let _77_1284 = (extract_pat g pat)
in (match (_77_1284) with
| (env, p) -> begin
(

let _77_1295 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(

let _77_1291 = (term_as_mlexpr env w)
in (match (_77_1291) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_77_1295) with
| (when_opt, f_when) -> begin
(

let _77_1299 = (term_as_mlexpr env branch)
in (match (_77_1299) with
| (mlbranch, f_branch, t_branch) -> begin
(FStar_All.pipe_right p (FStar_List.map (fun _77_1302 -> (match (_77_1302) with
| (p, wopt) -> begin
(

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

let _77_1311 = (let _166_416 = (let _166_415 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _166_415))
in (FStar_All.pipe_left FStar_Util.right _166_416))
in (match (_77_1311) with
| (fw, _77_1308, _77_1310) -> begin
(let _166_421 = (let _166_420 = (let _166_419 = (let _166_418 = (let _166_417 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_166_417)::[])
in (fw, _166_418))
in FStar_Extraction_ML_Syntax.MLE_App (_166_419))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _166_420))
in (_166_421, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| (_77_1314, _77_1316, (_77_1318, f_first, t_first))::rest -> begin
(

let _77_1344 = (FStar_List.fold_left (fun _77_1326 _77_1336 -> (match ((_77_1326, _77_1336)) with
| ((topt, f), (_77_1328, _77_1330, (_77_1332, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join f f_branch)
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
in (topt, f)))
end)) (Some (t_first), f_first) rest)
in (match (_77_1344) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _77_1355 -> (match (_77_1355) with
| (p, (wopt, _77_1348), (b, _77_1352, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_77_1358) -> begin
b
end)
in (p, wopt, b))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _166_425 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_166_425, f_match, t_match))))
end))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref 0)
in (fun x -> (

let _77_1368 = (FStar_Util.incr c)
in (let _166_428 = (FStar_ST.read c)
in (x, _166_428)))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _77_1376 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_77_1376) with
| (_77_1374, fstar_disc_type) -> begin
(

let wildcards = (match ((let _166_435 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _166_435.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _77_1379) -> begin
(let _166_439 = (FStar_All.pipe_right binders (FStar_List.filter (fun _77_4 -> (match (_77_4) with
| (_77_1384, Some (FStar_Syntax_Syntax.Implicit (_77_1386))) -> begin
true
end
| _77_1391 -> begin
false
end))))
in (FStar_All.pipe_right _166_439 (FStar_List.map (fun _77_1392 -> (let _166_438 = (fresh "_")
in (_166_438, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _77_1395 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _166_454 = (let _166_453 = (let _166_452 = (let _166_451 = (let _166_450 = (let _166_449 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _166_448 = (let _166_447 = (let _166_443 = (let _166_441 = (let _166_440 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_166_440, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_166_441))
in (let _166_442 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_166_443, None, _166_442)))
in (let _166_446 = (let _166_445 = (let _166_444 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _166_444))
in (_166_445)::[])
in (_166_447)::_166_446))
in (_166_449, _166_448)))
in FStar_Extraction_ML_Syntax.MLE_Match (_166_450))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _166_451))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _166_452))
in FStar_Extraction_ML_Syntax.MLE_Fun (_166_453))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _166_454))
in FStar_Extraction_ML_Syntax.MLM_Let ((false, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




