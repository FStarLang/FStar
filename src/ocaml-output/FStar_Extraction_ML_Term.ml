
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


let fail = (fun r msg -> (

let _77_17 = (let _168_29 = (let _168_28 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _168_28 msg))
in (FStar_All.pipe_left FStar_Util.print_string _168_29))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _77_23 -> (match (_77_23) with
| (vars, ty) -> begin
(let _168_37 = (let _168_36 = (FStar_Syntax_Print.term_to_string t)
in (let _168_35 = (let _168_33 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _168_33 (FStar_String.concat ", ")))
in (let _168_34 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _168_36 _168_35 _168_34))))
in (fail t.FStar_Syntax_Syntax.pos _168_37))
end))


let err_ill_typed_application = (fun env t args ty -> (let _168_47 = (let _168_46 = (FStar_Syntax_Print.term_to_string t)
in (let _168_45 = (let _168_43 = (FStar_All.pipe_right args (FStar_List.map (fun _77_31 -> (match (_77_31) with
| (x, _77_30) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _168_43 (FStar_String.concat " ")))
in (let _168_44 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _168_46 _168_45 _168_44))))
in (fail t.FStar_Syntax_Syntax.pos _168_47)))


let err_value_restriction = (fun t -> (let _168_51 = (let _168_50 = (FStar_Syntax_Print.tag_of_term t)
in (let _168_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _168_50 _168_49)))
in (fail t.FStar_Syntax_Syntax.pos _168_51)))


let err_unexpected_eff = (fun t f0 f1 -> (let _168_56 = (let _168_55 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _168_55 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _168_56)))


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
| Some (_77_45, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _77_50 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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
in (

let _77_67 = (FStar_Extraction_ML_UEnv.debug env (fun _77_65 -> (let _168_78 = (FStar_Syntax_Print.term_to_string t)
in (let _168_77 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _168_78 _168_77)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_77_70) -> begin
(let _168_83 = (let _168_82 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _168_82))
in (FStar_All.failwith _168_83))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_77_74) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _77_82; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_77_79); FStar_Syntax_Syntax.fv_qual = _77_77}) -> begin
(

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let _77_87 = (FStar_Extraction_ML_UEnv.debug env (fun _77_86 -> (match (()) with
| () -> begin
(let _168_86 = (FStar_Syntax_Print.term_to_string t)
in (let _168_85 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _168_86 _168_85)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _168_87 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _168_87))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _168_88 = (level env t)
in (FStar_All.pipe_left predecessor _168_88))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _77_110, _77_112) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_77_116) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _77_120) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _77_125) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_139) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_77_143, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_77_148, branches) -> begin
(match (branches) with
| ((_77_155, _77_157, e))::_77_153 -> begin
(level env e)
end
| _77_162 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _77_165) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _77_170) -> begin
(level env head)
end)))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _77_177 -> begin
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


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _168_97 = (FStar_Syntax_Subst.compress t)
in _168_97.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _77_203 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _168_100 = (FStar_Syntax_Subst.compress t)
in _168_100.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _77_224 -> (match (_77_224) with
| (te, _77_223) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _77_237 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_77_258, fields) -> begin
(FStar_Util.for_all (fun _77_265 -> (match (_77_265) with
| (_77_263, e) -> begin
(is_ml_value e)
end)) fields)
end
| _77_267 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _77_280 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _168_113 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _168_113))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = (false, None, None)
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(

let _77_287 = (FStar_List.hd l)
in (match (_77_287) with
| (p1, w1, e1) -> begin
(

let _77_291 = (let _168_116 = (FStar_List.tl l)
in (FStar_List.hd _168_116))
in (match (_77_291) with
| (p2, w2, e2) -> begin
(match ((w1, w2, p1.FStar_Syntax_Syntax.v, p2.FStar_Syntax_Syntax.v)) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
(true, Some (e1), Some (e2))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
(true, Some (e2), Some (e1))
end
| _77_311 -> begin
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
| _77_332 -> begin
(

let _77_334 = (FStar_Extraction_ML_UEnv.debug g (fun _77_333 -> (match (()) with
| () -> begin
(let _168_146 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _168_145 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _168_144 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _168_146 _168_145 _168_144))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, ty, expect)))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_77_339, t) -> begin
t
end
| _77_344 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _168_167 = (let _168_166 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _168_166))
in (FStar_All.failwith _168_167))
end
| FStar_Syntax_Syntax.Tm_uvar (_77_362) -> begin
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

let _77_398 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_398) with
| (bs, c) -> begin
(

let _77_401 = (binders_as_ml_binders env bs)
in (match (_77_401) with
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

let _77_418 = (FStar_List.fold_right (fun _77_411 _77_414 -> (match ((_77_411, _77_414)) with
| ((_77_409, t), (tag, t')) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((t, tag, t')))
end)) mlbs (erase, t_ret))
in (match (_77_418) with
| (_77_416, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _168_170 = (FStar_Syntax_Util.un_uinst head)
in _168_170.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _168_171 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, (FStar_List.append args' args)))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _168_171))
end
| _77_432 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _77_437) -> begin
(

let _77_442 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_77_442) with
| (bs, ty) -> begin
(

let _77_445 = (binders_as_ml_binders env bs)
in (match (_77_445) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _77_459 -> (match (_77_459) with
| (a, _77_458) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _77_465 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_77_465) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _77_471 = (FStar_Util.first_N n_args formals)
in (match (_77_471) with
| (_77_469, rest) -> begin
(let _168_178 = (FStar_List.map (fun _77_472 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _168_178))
end))
end else begin
mlargs
end)
in (let _168_180 = (let _168_179 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mlargs, _168_179))
in FStar_Extraction_ML_Syntax.MLTY_Named (_168_180))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _77_490 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _77_479 b -> (match (_77_479) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _168_185 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_168_185, FStar_Extraction_ML_Syntax.ml_unit_ty))
in ((ml_b)::ml_bs, env))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b ([], t) false false false)
in (

let ml_b = (let _168_186 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in (_168_186, t))
in ((ml_b)::ml_bs, env)))))
end
end)) ([], g)))
in (match (_77_490) with
| (ml_bs, env) -> begin
((FStar_List.rev ml_bs), env)
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match ((e1.FStar_Extraction_ML_Syntax.expr, e2.FStar_Extraction_ML_Syntax.expr)) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _77_501) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_77_504, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _77_509 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NoLetQualifier, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _77_524 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _77_526 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _77_528 -> begin
FStar_Extraction_ML_Syntax.MLE_Let ((lbs, body))
end)
end
| _77_530 -> begin
FStar_Extraction_ML_Syntax.MLE_Let ((lbs, body))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _77_540 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_77_542, fns)) -> begin
(

let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (

let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _77_550 -> begin
p
end)
end)
end
| _77_552 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(type_leq g t t')
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_77_568) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) when (not ((FStar_Options.use_native_int ()))) -> begin
(

let i = FStar_Const.Const_int ((c, None))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _168_227 = (let _168_226 = (let _168_225 = (let _168_224 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _168_223 = (let _168_222 = (let _168_221 = (let _168_220 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _168_219 -> FStar_Extraction_ML_Syntax.MLE_Const (_168_219)) _168_220))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _168_221))
in (_168_222)::[])
in (_168_224)::_168_223))
in (FStar_Extraction_ML_Util.prims_op_equality, _168_225))
in FStar_Extraction_ML_Syntax.MLE_App (_168_226))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _168_227))
in (let _168_228 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in (g, Some ((FStar_Extraction_ML_Syntax.MLP_Var (x), (when_clause)::[])), _168_228)))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_Tc.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _168_233 = (let _168_231 = (let _168_230 = (let _168_229 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_168_229))
in (_168_230, []))
in Some (_168_231))
in (let _168_232 = (ok mlty)
in (g, _168_233, _168_232)))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _168_238 = if imp then begin
None
end else begin
(let _168_236 = (let _168_235 = (let _168_234 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_168_234))
in (_168_235, []))
in Some (_168_236))
end
in (let _168_237 = (ok mlty)
in (g, _168_238, _168_237)))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
(g, Some ((FStar_Extraction_ML_Syntax.MLP_Wild, [])), true)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false imp)
in (let _168_243 = if imp then begin
None
end else begin
(let _168_241 = (let _168_240 = (let _168_239 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_168_239))
in (_168_240, []))
in Some (_168_241))
end
in (let _168_242 = (ok mlty)
in (g, _168_243, _168_242)))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_77_593) -> begin
(g, None, true)
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _77_615 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _77_602; FStar_Extraction_ML_Syntax.loc = _77_600}, ttys, _77_608) -> begin
(n, ttys)
end
| _77_612 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_77_615) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _77_619 = (FStar_Util.first_N nTyVars pats)
in (match (_77_619) with
| (tysVarPats, restPats) -> begin
(

let pat_ty_compat = (match (expected_topt) with
| None -> begin
true
end
| Some (expected_t) -> begin
try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _77_632 -> (match (_77_632) with
| (p, _77_631) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_77_634, t) -> begin
(term_as_mlty g t)
end
| _77_639 -> begin
(Prims.raise Un_extractable)
end)
end))))
in (

let pat_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (type_leq g pat_ty expected_t)))
end)
with
| Un_extractable -> begin
false
end
end)
in (

let _77_654 = (FStar_Util.fold_map (fun g _77_646 -> (match (_77_646) with
| (p, imp) -> begin
(

let _77_651 = (extract_one_pat disjunctive_pat true g p None)
in (match (_77_651) with
| (g, p, _77_650) -> begin
(g, p)
end))
end)) g tysVarPats)
in (match (_77_654) with
| (g, tyMLPats) -> begin
(

let _77_666 = (FStar_Util.fold_map (fun g _77_658 -> (match (_77_658) with
| (p, imp) -> begin
(

let _77_663 = (extract_one_pat disjunctive_pat false g p None)
in (match (_77_663) with
| (g, p, _77_662) -> begin
(g, p)
end))
end)) g restPats)
in (match (_77_666) with
| (g, restMLPats) -> begin
(

let _77_674 = (let _168_252 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _77_2 -> (match (_77_2) with
| Some (x) -> begin
(x)::[]
end
| _77_671 -> begin
[]
end))))
in (FStar_All.pipe_right _168_252 FStar_List.split))
in (match (_77_674) with
| (mlPats, when_clauses) -> begin
(let _168_256 = (let _168_255 = (let _168_254 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor ((d, mlPats))))
in (let _168_253 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in (_168_254, _168_253)))
in Some (_168_255))
in (g, _168_256, pat_ty_compat))
end))
end))
end)))
end)))
end))
end)))
in (

let extract_one_pat = (fun disj g p expected_t -> (match ((extract_one_pat disj false g p expected_t)) with
| (g, Some (x, v), b) -> begin
(g, (x, v), b)
end
| _77_688 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _168_267 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_168_267))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _77_704 = (extract_one_pat true g p (Some (expected_t)))
in (match (_77_704) with
| (g, p, b) -> begin
(

let _77_714 = (FStar_Util.fold_map (fun b p -> (

let _77_711 = (extract_one_pat true g p (Some (expected_t)))
in (match (_77_711) with
| (_77_708, p, b') -> begin
((b && b'), p)
end))) b pats)
in (match (_77_714) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _77_729 = (FStar_All.pipe_right ps (FStar_List.partition (fun _77_3 -> (match (_77_3) with
| (_77_718, (_77_722)::_77_720) -> begin
true
end
| _77_726 -> begin
false
end))))
in (match (_77_729) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _77_732 -> (match (_77_732) with
| (x, whens) -> begin
(let _168_272 = (mk_when_clause whens)
in (x, _168_272))
end))))
in (

let res = (match (rest) with
| [] -> begin
(g, ps, b)
end
| rest -> begin
(let _168_276 = (let _168_275 = (let _168_274 = (let _168_273 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_168_273))
in (_168_274, None))
in (_168_275)::ps)
in (g, _168_276, b))
end)
in res))
end)))
end))
end))
end
| _77_738 -> begin
(

let _77_744 = (extract_one_pat false g p (Some (expected_t)))
in (match (_77_744) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in (g, ((p, when_clause))::[], b))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _77_755, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _168_291 = (let _168_290 = (let _168_289 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((x, t0), _168_289))
in (_168_290)::more_args)
in (eta_args _168_291 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_77_761, _77_763) -> begin
((FStar_List.rev more_args), t)
end
| _77_767 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match ((e.FStar_Extraction_ML_Syntax.expr, qual)) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_77_772, args), Some (FStar_Syntax_Syntax.Record_ctor (_77_777, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record ((path, fields))))))
end
| _77_786 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _77_792 = (eta_args [] residualType)
in (match (_77_792) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _168_300 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _168_300))
end
| _77_795 -> begin
(

let _77_798 = (FStar_List.unzip eargs)
in (match (_77_798) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _168_302 = (let _168_301 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor ((head, (FStar_List.append args eargs)))))
in (FStar_All.pipe_left (as_record qual) _168_301))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _168_302))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun ((binders, body)))))
end
| _77_805 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr, qual)) with
| (_77_807, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _77_813; FStar_Extraction_ML_Syntax.loc = _77_811}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj ((mle, fn))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _77_830 -> begin
(let _168_304 = (let _168_303 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in (_168_303, args))
in FStar_Extraction_ML_Syntax.MLE_App (_168_304))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _168_305 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, mlargs))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _168_305))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _168_306 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, []))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _168_306))
end
| _77_870 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _77_879 = (term_as_mlexpr' g t)
in (match (_77_879) with
| (e, tag, ty) -> begin
(

let _77_881 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _168_331 = (let _168_330 = (FStar_Syntax_Print.tag_of_term t)
in (let _168_329 = (FStar_Syntax_Print.term_to_string t)
in (let _168_328 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "term_as_mlexpr (%s) :  %s has ML type %s\n" _168_330 _168_329 _168_328))))
in (FStar_Util.print_string _168_331))))
in (erase g e ty tag))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _77_889 = (check_term_as_mlexpr' g t f ty)
in (match (_77_889) with
| (e, t) -> begin
(

let _77_894 = (erase g e t f)
in (match (_77_894) with
| (r, _77_892, t) -> begin
(r, t)
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _77_902 = (term_as_mlexpr g e0)
in (match (_77_902) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _168_340 = (maybe_coerce g e t ty)
in (_168_340, ty))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _77_907 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _168_346 = (let _168_345 = (FStar_Syntax_Print.tag_of_term top)
in (let _168_344 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _168_345 _168_344)))
in (FStar_Util.print_string _168_346))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _168_348 = (let _168_347 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _168_347))
in (FStar_All.failwith _168_348))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NoLetQualifier, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((FStar_Extraction_ML_Syntax.Mutable, bodies), continuation)); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ)
end
| _77_947 -> begin
(FStar_All.failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _168_349 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _168_349 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _77_968 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_77_968) with
| (comp_1, _77_965, _77_967) -> begin
(

let _77_987 = (

let k = (let _168_352 = (let _168_351 = (let _168_350 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _168_350 FStar_Syntax_Syntax.mk_binder))
in (_168_351)::[])
in (FStar_Syntax_Util.abs _168_352 body None))
in (

let _77_974 = (term_as_mlexpr g k)
in (match (_77_974) with
| (ml_k, _77_972, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_77_976, _77_978, m_2) -> begin
m_2
end
| _77_983 -> begin
(FStar_All.failwith "Impossible")
end)
in (ml_k, m_2))
end)))
in (match (_77_987) with
| (ml_k, ty) -> begin
(

let bind = (let _168_355 = (let _168_354 = (let _168_353 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _168_353 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_168_354))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _168_355))
in (let _168_356 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App ((bind, (comp_1)::(ml_k)::[]))))
in (_168_356, FStar_Extraction_ML_Syntax.E_IMPURE, ty)))
end))
end)))
end)
end
| _77_990 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _77_1007 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_77_1007) with
| (_77_1003, ty, _77_1006) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _168_360 = (let _168_359 = (let _168_358 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _168_357 -> FStar_Extraction_ML_Syntax.MLE_Const (_168_357)) _168_358))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _168_359))
in (_168_360, FStar_Extraction_ML_Syntax.E_PURE, ml_ty)))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_77_1016), _77_1019) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty)
end
| (FStar_Util.Inr (x, mltys, _77_1024), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE, t)
end
| ([], t) -> begin
(let _168_361 = (maybe_eta_data_and_project_record g qual t x)
in (_168_361, FStar_Extraction_ML_Syntax.E_PURE, t))
end
| _77_1036 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _77_1044 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_1044) with
| (bs, body) -> begin
(

let _77_1047 = (binders_as_ml_binders g bs)
in (match (_77_1047) with
| (ml_bs, env) -> begin
(

let _77_1051 = (term_as_mlexpr env body)
in (match (_77_1051) with
| (ml_body, f, t) -> begin
(

let _77_1061 = (FStar_List.fold_right (fun _77_1055 _77_1058 -> (match ((_77_1055, _77_1058)) with
| ((_77_1053, targ), (f, t)) -> begin
(FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.MLTY_Fun ((targ, f, t)))
end)) ml_bs (f, t))
in (match (_77_1061) with
| (f, tfun) -> begin
(let _168_364 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun ((ml_bs, ml_body))))
in (_168_364, f, tfun))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _77_1067; FStar_Syntax_Syntax.pos = _77_1065; FStar_Syntax_Syntax.vars = _77_1063}, (t)::[]) -> begin
(

let _77_1078 = (term_as_mlexpr' g (Prims.fst t))
in (match (_77_1078) with
| (ml, e_tag, mlty) -> begin
(ml, FStar_Extraction_ML_Syntax.E_PURE, mlty)
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_77_1086)); FStar_Syntax_Syntax.tk = _77_1084; FStar_Syntax_Syntax.pos = _77_1082; FStar_Syntax_Syntax.vars = _77_1080}, (t)::[]) -> begin
(

let _77_1097 = (term_as_mlexpr' g (Prims.fst t))
in (match (_77_1097) with
| (ml, e_tag, mlty) -> begin
(ml, FStar_Extraction_ML_Syntax.E_IMPURE, mlty)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_77_1103) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _77_1107 -> begin
(

let rec extract_app = (fun is_data _77_1112 _77_1115 restArgs -> (match ((_77_1112, _77_1115)) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match ((restArgs, t)) with
| ([], _77_1119) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = 1) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _77_1128; FStar_Syntax_Syntax.p = _77_1126}; FStar_Syntax_Syntax.fv_delta = _77_1124; FStar_Syntax_Syntax.fv_qual = _77_1122}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _77_1134 -> begin
false
end))
in (

let _77_1145 = if evaluation_order_guaranteed then begin
(let _168_373 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in ([], _168_373))
end else begin
(FStar_List.fold_left (fun _77_1138 _77_1141 -> (match ((_77_1138, _77_1141)) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
(lbs, (arg)::out_args)
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _168_377 = (let _168_376 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_168_376)::out_args)
in (((x, arg))::lbs, _168_377)))
end
end)) ([], []) mlargs_f)
end
in (match (_77_1145) with
| (lbs, mlargs) -> begin
(

let app = (let _168_378 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App ((mlhead, mlargs))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _168_378))
in (

let l_app = (FStar_List.fold_right (fun _77_1149 out -> (match (_77_1149) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false (FStar_Extraction_ML_Syntax.NoLetQualifier, ({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some (([], arg.FStar_Extraction_ML_Syntax.mlty)); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[]) out))
end)) lbs app)
in (l_app, f, t)))
end)))
end
| (((arg, _77_1155))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _168_382 = (let _168_381 = (FStar_Extraction_ML_Util.join f f')
in (_168_381, t))
in (extract_app is_data (mlhead, ((FStar_Extraction_ML_Syntax.ml_unit, FStar_Extraction_ML_Syntax.E_PURE))::mlargs_f) _168_382 rest))
end else begin
(let _168_387 = (let _168_386 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _168_385 = (FStar_Syntax_Print.term_to_string arg)
in (let _168_384 = (FStar_Syntax_Print.tag_of_term arg)
in (let _168_383 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _168_386 _168_385 _168_384 _168_383)))))
in (FStar_All.failwith _168_387))
end
end
| (((e0, _77_1167))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let _77_1179 = (term_as_mlexpr g e0)
in (match (_77_1179) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _168_389 = (let _168_388 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in (_168_388, t))
in (extract_app is_data (mlhead, ((e0, f0))::mlargs_f) _168_389 rest)))
end))
end
| _77_1182 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data (mlhead, mlargs_f) (f, t) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t)
end)
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead _77_1191 args -> (match (_77_1191) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_77_1194)) -> begin
(

let rec remove_implicits = (fun args f t -> (match ((args, t)) with
| (((_77_1203, Some (FStar_Syntax_Syntax.Implicit (_77_1205))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_77_1211, f', t)) -> begin
(let _168_404 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _168_404 t))
end
| _77_1218 -> begin
(args, f, t)
end))
in (

let _77_1222 = (remove_implicits args f t)
in (match (_77_1222) with
| (args, f, t) -> begin
(extract_app is_data (mlhead, []) (f, t) args)
end)))
end
| _77_1224 -> begin
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

let _77_1245 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
(u, q)
end
| _77_1237 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_77_1245) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _77_1250))::_77_1247 -> begin
(is_type g a)
end
| _77_1254 -> begin
false
end)
in (

let _77_1300 = (match (vars) with
| (_77_1259)::_77_1257 when ((not (has_typ_apps)) && inst_ok) -> begin
(head_ml, t, args)
end
| _77_1262 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _77_1266 = (FStar_Util.first_N n args)
in (match (_77_1266) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _77_1270 -> (match (_77_1270) with
| (x, _77_1269) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate (vars, t) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _77_1279 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _77_1279.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _77_1279.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _77_1285; FStar_Extraction_ML_Syntax.loc = _77_1283})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App (((

let _77_1292 = head
in {FStar_Extraction_ML_Syntax.expr = _77_1292.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, t)); FStar_Extraction_ML_Syntax.loc = _77_1292.FStar_Extraction_ML_Syntax.loc}), (FStar_Extraction_ML_Syntax.ml_unit)::[]))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _77_1295 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in (head, t, rest))))
end))
end else begin
(err_uninst g head (vars, t))
end)
end)
in (match (_77_1300) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _168_406 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in (_168_406, FStar_Extraction_ML_Syntax.E_PURE, head_t))
end
| _77_1303 -> begin
(extract_app_maybe_projector qual head_ml (FStar_Extraction_ML_Syntax.E_PURE, head_t) args)
end)
end)))
end))
end
| _77_1305 -> begin
(

let _77_1309 = (term_as_mlexpr g head)
in (match (_77_1309) with
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

let _77_1326 = (check_term_as_mlexpr g e0 f t)
in (match (_77_1326) with
| (e, t) -> begin
(e, f, t)
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _77_1342 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, e')
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _168_407 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _168_407))
in (

let lb = (

let _77_1336 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _77_1336.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _77_1336.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _77_1336.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _77_1336.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((0, x)))::[]) e')
in ((lb)::[], e')))))
end
end
in (match (_77_1342) with
| (lbs, e') -> begin
(

let maybe_generalize = (fun _77_1350 -> (match (_77_1350) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _77_1348; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _168_410 = (FStar_List.hd bs)
in (FStar_All.pipe_right _168_410 (is_type_binder g))) -> begin
(

let _77_1359 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_1359) with
| (bs, c) -> begin
(

let _77_1369 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
(bs, (FStar_Syntax_Util.comp_result c))
end
| Some (bs, b, rest) -> begin
(let _168_412 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in (bs, _168_412))
end)
in (match (_77_1369) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _77_1375) -> begin
(

let _77_1380 = (FStar_Syntax_Subst.open_term bs body)
in (match (_77_1380) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _77_1383 = (FStar_Util.first_N n_tbinders bs)
in (match (_77_1383) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _77_1387 _77_1391 -> (match ((_77_1387, _77_1391)) with
| ((x, _77_1386), (y, _77_1390)) -> begin
(let _168_416 = (let _168_415 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _168_415))
in FStar_Syntax_Syntax.NT (_168_416))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _77_1398 -> (match (_77_1398) with
| (a, _77_1397) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _168_420 = (FStar_All.pipe_right targs (FStar_List.map (fun _77_1404 -> (match (_77_1404) with
| (x, _77_1403) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_168_420, expected_t))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _77_1408 -> begin
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
| _77_1413 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in (lbname_, f_e, (t, (targs, polytype)), add_unit, body))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env _77_1428 -> (match (_77_1428) with
| (a, _77_1427) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _168_424 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _77_1434 -> (match (_77_1434) with
| (x, _77_1433) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in (_168_424, expected_t))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _77_1439 -> (match (_77_1439) with
| (bv, _77_1438) -> begin
(let _168_426 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _168_426 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((e, args))) None e.FStar_Syntax_Syntax.pos)
in (lbname_, f_e, (t, (tbinders, polytype)), false, e))))))
end
| _77_1443 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _77_1445 -> begin
(

let expected_t = (term_as_mlty g t)
in (lbname_, f_e, (t, ([], ([], expected_t))), false, e))
end)))
end))
in (

let check_lb = (fun env _77_1460 -> (match (_77_1460) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _77_1465 -> (match (_77_1465) with
| (a, _77_1464) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.ml_unit_ty, FStar_Extraction_ML_Syntax.E_PURE, (Prims.snd polytype)))
end else begin
(Prims.snd polytype)
end
in (

let _77_1471 = (check_term_as_mlexpr env e f expected_t)
in (match (_77_1471) with
| (e, _77_1470) -> begin
(f, {FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _77_1495 = (FStar_List.fold_right (fun lb _77_1476 -> (match (_77_1476) with
| (env, lbs) -> begin
(

let _77_1489 = lb
in (match (_77_1489) with
| (lbname, _77_1479, (t, (_77_1482, polytype)), add_unit, _77_1488) -> begin
(

let _77_1492 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_77_1492) with
| (env, nm) -> begin
(env, ((nm, lb))::lbs)
end))
end))
end)) lbs (g, []))
in (match (_77_1495) with
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

let _77_1501 = (term_as_mlexpr env_body e')
in (match (_77_1501) with
| (e', f', t') -> begin
(

let f = (let _168_436 = (let _168_435 = (FStar_List.map Prims.fst lbs)
in (f')::_168_435)
in (FStar_Extraction_ML_Util.join_l _168_436))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NoLetQualifier
end
in (let _168_441 = (let _168_440 = (let _168_438 = (let _168_437 = (FStar_List.map Prims.snd lbs)
in (is_rec, _168_437))
in (mk_MLE_Let top_level _168_438 e'))
in (let _168_439 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _168_440 _168_439)))
in (_168_441, f, t'))))
end))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _77_1511 = (term_as_mlexpr g scrutinee)
in (match (_77_1511) with
| (e, f_e, t_e) -> begin
(

let _77_1515 = (check_pats_for_ite pats)
in (match (_77_1515) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match ((then_e, else_e)) with
| (Some (then_e), Some (else_e)) -> begin
(

let _77_1527 = (term_as_mlexpr g then_e)
in (match (_77_1527) with
| (then_mle, f_then, t_then) -> begin
(

let _77_1531 = (term_as_mlexpr g else_e)
in (match (_77_1531) with
| (else_mle, f_else, t_else) -> begin
(

let _77_1534 = if (type_leq g t_then t_else) then begin
(t_else, no_lift)
end else begin
if (type_leq g t_else t_then) then begin
(t_then, no_lift)
end else begin
(FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.apply_obj_repr)
end
end
in (match (_77_1534) with
| (t_branch, maybe_lift) -> begin
(let _168_472 = (let _168_470 = (let _168_469 = (let _168_468 = (maybe_lift then_mle t_then)
in (let _168_467 = (let _168_466 = (maybe_lift else_mle t_else)
in Some (_168_466))
in (e, _168_468, _168_467)))
in FStar_Extraction_ML_Syntax.MLE_If (_168_469))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _168_470))
in (let _168_471 = (FStar_Extraction_ML_Util.join f_then f_else)
in (_168_472, _168_471, t_branch)))
end))
end))
end))
end
| _77_1536 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _77_1568 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _77_1542 = (FStar_Syntax_Subst.open_branch br)
in (match (_77_1542) with
| (pat, when_opt, branch) -> begin
(

let _77_1546 = (extract_pat g pat t_e)
in (match (_77_1546) with
| (env, p, pat_t_compat) -> begin
(

let _77_1557 = (match (when_opt) with
| None -> begin
(None, FStar_Extraction_ML_Syntax.E_PURE)
end
| Some (w) -> begin
(

let _77_1553 = (term_as_mlexpr env w)
in (match (_77_1553) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in (Some (w), f_w))
end))
end)
in (match (_77_1557) with
| (when_opt, f_when) -> begin
(

let _77_1561 = (term_as_mlexpr env branch)
in (match (_77_1561) with
| (mlbranch, f_branch, t_branch) -> begin
(let _168_476 = (FStar_All.pipe_right p (FStar_List.map (fun _77_1564 -> (match (_77_1564) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in (p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
end))))
in ((compat && pat_t_compat), _168_476))
end))
end))
end))
end))) true))
in (match (_77_1568) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = if pat_t_compat then begin
e
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t_e, FStar_Extraction_ML_Syntax.MLTY_Top))))
end
in (match (mlbranches) with
| [] -> begin
(

let _77_1577 = (let _168_478 = (let _168_477 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _168_477))
in (FStar_All.pipe_left FStar_Util.right _168_478))
in (match (_77_1577) with
| (fw, _77_1574, _77_1576) -> begin
(let _168_483 = (let _168_482 = (let _168_481 = (let _168_480 = (let _168_479 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_168_479)::[])
in (fw, _168_480))
in FStar_Extraction_ML_Syntax.MLE_App (_168_481))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _168_482))
in (_168_483, FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.ml_unit_ty))
end))
end
| ((_77_1580, _77_1582, (_77_1584, f_first, t_first)))::rest -> begin
(

let _77_1610 = (FStar_List.fold_left (fun _77_1592 _77_1602 -> (match ((_77_1592, _77_1602)) with
| ((topt, f), (_77_1594, _77_1596, (_77_1598, f_branch, t_branch))) -> begin
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
in (match (_77_1610) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _77_1621 -> (match (_77_1621) with
| (p, (wopt, _77_1614), (b, _77_1618, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_77_1624) -> begin
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
in (let _168_487 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match ((e, mlbranches))))
in (_168_487, f_match, t_match))))
end))
end)))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref 0)
in (fun x -> (

let _77_1634 = (FStar_Util.incr c)
in (let _168_490 = (FStar_ST.read c)
in (x, _168_490)))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _77_1642 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_77_1642) with
| (_77_1640, fstar_disc_type) -> begin
(

let wildcards = (match ((let _168_497 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _168_497.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _77_1645) -> begin
(let _168_501 = (FStar_All.pipe_right binders (FStar_List.filter (fun _77_4 -> (match (_77_4) with
| (_77_1650, Some (FStar_Syntax_Syntax.Implicit (_77_1652))) -> begin
true
end
| _77_1657 -> begin
false
end))))
in (FStar_All.pipe_right _168_501 (FStar_List.map (fun _77_1658 -> (let _168_500 = (fresh "_")
in (_168_500, FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
| _77_1661 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _168_516 = (let _168_515 = (let _168_514 = (let _168_513 = (let _168_512 = (let _168_511 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name (([], (FStar_Extraction_ML_Syntax.idsym mlid)))))
in (let _168_510 = (let _168_509 = (let _168_505 = (let _168_503 = (let _168_502 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in (_168_502, (FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in FStar_Extraction_ML_Syntax.MLP_CTor (_168_503))
in (let _168_504 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (_168_505, None, _168_504)))
in (let _168_508 = (let _168_507 = (let _168_506 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in (FStar_Extraction_ML_Syntax.MLP_Wild, None, _168_506))
in (_168_507)::[])
in (_168_509)::_168_508))
in (_168_511, _168_510)))
in FStar_Extraction_ML_Syntax.MLE_Match (_168_512))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _168_513))
in ((FStar_List.append wildcards (((mlid, targ))::[])), _168_514))
in FStar_Extraction_ML_Syntax.MLE_Fun (_168_515))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _168_516))
in FStar_Extraction_ML_Syntax.MLM_Let ((FStar_Extraction_ML_Syntax.NoLetQualifier, ({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[])))))))
end)))




