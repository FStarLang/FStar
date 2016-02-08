
open Prims
let binderIsExp : FStar_Absyn_Syntax.binder  ->  Prims.bool = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))

let rec argIsExp : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.bool Prims.list = (fun k typeName -> (match ((let _180_7 = (FStar_Absyn_Util.compress_kind k)
in _180_7.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _180_9 = (FStar_List.map binderIsExp bs)
in (let _180_8 = (argIsExp r typeName)
in (FStar_List.append _180_9 _180_8)))
end
| FStar_Absyn_Syntax.Kind_delayed (k, _78_13, _78_15) -> begin
(FStar_All.failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_78_19, k) -> begin
(argIsExp k typeName)
end
| _78_24 -> begin
(FStar_All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))

let numIndices : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.nat = (fun k typeName -> (let _180_14 = (argIsExp k typeName)
in (FStar_List.length _180_14)))

let mlty_of_isExp : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlty = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)

let delta_norm_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (let cache = (FStar_Util.smap_create 20)
in (let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(let res = (match ((FStar_Tc_Env.lookup_effect_abbrev g.FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some (_78_37, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (let _78_42 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in delta_norm_eff))

let translate_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g l -> (let l = (delta_norm_eff g l)
in if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))

let rec curry : FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun inp f out -> (match (inp) with
| [] -> begin
out
end
| h::[] -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _180_34 = (let _180_33 = (curry ((h2)::tl) f out)
in (h1, FStar_Extraction_ML_Syntax.E_PURE, _180_33))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_180_34))
end))

type context =
FStar_Extraction_ML_Env.env

let extendContextWithRepAsTyVar : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either)  ->  context  ->  context = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_78_68)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false false)
end
| _78_72 -> begin
(FStar_All.failwith "Impossible case")
end))

let extendContextWithRepAsTyVars : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either) Prims.list  ->  context  ->  context = (fun b c -> (FStar_List.fold_right extendContextWithRepAsTyVar b c))

let extendContextAsTyvar : Prims.bool  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either  ->  context  ->  context = (fun availableInML b c -> (match (b) with
| FStar_Util.Inl (bt) -> begin
(FStar_Extraction_ML_Env.extend_ty c bt (Some (if availableInML then begin
FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt))
end else begin
FStar_Extraction_ML_Env.unknownType
end)))
end
| FStar_Util.Inr (bv) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false false)
end))

let extendContext : context  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  context = (fun c tyVars -> (FStar_List.fold_right (extendContextAsTyvar true) tyVars c))

let isTypeScheme : FStar_Ident.lident  ->  context  ->  Prims.bool = (fun i c -> true)

let preProcType : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun c ft -> (let ft = (FStar_Absyn_Util.compress_typ ft)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) c.FStar_Extraction_ML_Env.tcenv ft)))

let extractTyVar : context  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun c btv -> (FStar_Extraction_ML_Env.lookup_tyvar c btv))

let rec extractTyp : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> (let ft = (preProcType c ft)
in (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| FStar_Absyn_Syntax.Typ_fun (bs, codomain) -> begin
(let _78_104 = (extractBindersTypes c bs)
in (match (_78_104) with
| (bts, newC) -> begin
(let _78_107 = (extractComp newC codomain)
in (match (_78_107) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _78_110) -> begin
(extractTyp c bv.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_app (ty, arrgs) -> begin
(let ty = (preProcType c ty)
in (let res = (match (ty.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| FStar_Absyn_Syntax.Typ_app (tyin, argsin) -> begin
(let _180_86 = (FStar_Extraction_ML_Util.mkTypApp tyin (FStar_List.append argsin arrgs) ty)
in (extractTyp c _180_86))
end
| _78_127 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(let _78_135 = (extractBindersTypes c bs)
in (match (_78_135) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _78_138) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_78_144) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_78_147) -> begin
(FStar_All.failwith "expected the argument to be compressed")
end
| _78_150 -> begin
(FStar_All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg : context  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_78_156) -> begin
FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta : context  ->  FStar_Absyn_Syntax.meta_t  ->  FStar_Extraction_ML_Syntax.mlty = (fun c mt -> (match (mt) with
| (FStar_Absyn_Syntax.Meta_pattern (t, _)) | (FStar_Absyn_Syntax.Meta_named (t, _)) | (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _)) | (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _)) | (FStar_Absyn_Syntax.Meta_slack_formula (t, _, _)) -> begin
(extractTyp c t)
end))
and extractTyConstApp : context  ->  FStar_Absyn_Syntax.ftvar  ->  FStar_Absyn_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ftv ags -> if (isTypeScheme ftv.FStar_Absyn_Syntax.v c) then begin
(let mlargs = (FStar_List.map (getTypeFromArg c) ags)
in (let k = ftv.FStar_Absyn_Syntax.sort
in (let ar = (argIsExp k ftv.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _78_198 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_78_198) with
| (_78_196, missingArgs) -> begin
(let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _180_98 = (let _180_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in ((FStar_List.append mlargs argCompletion), _180_97))
in FStar_Extraction_ML_Syntax.MLTY_Named (_180_98)))
end)))))
end else begin
(FStar_All.failwith "this case was not anticipated")
end)
and extractBinderType : context  ->  FStar_Absyn_Syntax.binder  ->  (FStar_Extraction_ML_Syntax.mlty * context) = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _78_205) -> begin
(let _180_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _180_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in (_180_102, _180_101)))
end
| (FStar_Util.Inr (bvv), _78_210) -> begin
(let _180_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _180_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in (_180_104, _180_103)))
end))
and extractBindersTypes : context  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * context) = (fun c bs -> (let _180_110 = (FStar_List.fold_left (fun _78_216 b -> (match (_78_216) with
| (lt, cp) -> begin
(let _78_220 = (extractBinderType cp b)
in (match (_78_220) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _78_223 -> (match (_78_223) with
| (x, c) -> begin
((FStar_List.rev x), c)
end)) _180_110)))
and extractKind : context  ->  FStar_Absyn_Syntax.knd  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> FStar_Extraction_ML_Env.erasedContent)
and extractComp : context  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (extractComp' c ft.FStar_Absyn_Syntax.n))
and extractComp' : context  ->  FStar_Absyn_Syntax.comp'  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (match (ft) with
| FStar_Absyn_Syntax.Total (ty) -> begin
(let _180_117 = (extractTyp c ty)
in (_180_117, FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Absyn_Syntax.Comp (cm) -> begin
(let _180_119 = (extractTyp c cm.FStar_Absyn_Syntax.result_typ)
in (let _180_118 = (translate_eff c cm.FStar_Absyn_Syntax.effect_name)
in (_180_119, _180_118)))
end))

let binderPPnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _78_238) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _78_243) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))

let binderRealnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _78_249) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _78_254) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end))

let mlsymbolOfLident : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

type inductiveConstructor =
{cname : FStar_Ident.lident; ctype : FStar_Absyn_Syntax.typ}

let is_MkinductiveConstructor : inductiveConstructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveConstructor"))))

type inductiveTypeFam =
{tyName : FStar_Ident.lident; k : FStar_Absyn_Syntax.knd; tyBinders : FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : FStar_Absyn_Syntax.qualifier Prims.list}

let is_MkinductiveTypeFam : inductiveTypeFam  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveTypeFam"))))

type typeAbbrev =
{abTyName : FStar_Ident.lident; abTyBinders : FStar_Absyn_Syntax.binders; abBody : FStar_Absyn_Syntax.typ}

let is_MktypeAbbrev : typeAbbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MktypeAbbrev"))))

let lookupDataConType : context  ->  FStar_Absyn_Syntax.sigelts  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun c sigb l -> (let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_78_277, tps, _78_280), quals, lids, _78_285) -> begin
if (l = l') then begin
(let t = (let _180_167 = (FStar_List.map (fun _78_291 -> (match (_78_291) with
| (x, _78_290) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _180_167 t))
in Some (t))
end else begin
None
end
end
| _78_294 -> begin
None
end)))
in (FStar_Util.must tr)))

let parseInductiveConstructors : context  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelts  ->  inductiveConstructor Prims.list = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _180_175 = (lookupDataConType c sigb h)
in {cname = h; ctype = _180_175})) cnames))

let rec parseInductiveTypesFromSigBundle : context  ->  FStar_Absyn_Syntax.sigelts  ->  (inductiveTypeFam Prims.list * typeAbbrev Prims.list * inductiveConstructor Prims.list) = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _78_308, constrs, qs, _78_312)::tlsig -> begin
(let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (let _78_320 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_78_320) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, _78_324, tc, quals, lids, _78_329)::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (let _78_334 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end else begin
([], [], [])
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _78_340, t, _78_343, _78_345)::tlsig -> begin
(let _78_352 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_78_352) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _180_181 = (let _180_180 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _180_180))
in (FStar_All.failwith _180_181))
end))

let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _78_359, b) -> begin
(let _180_184 = (argTypes b)
in (a)::_180_184)
end
| _78_364 -> begin
[]
end))

let lident2mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun l -> l.FStar_Ident.ident.FStar_Ident.idText)

let totalType_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _78_370 -> begin
(FStar_All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

let allBindersOfFuntype : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.binder Prims.list = (fun c t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _78_379 -> begin
[]
end)))

let bindersOfFuntype : context  ->  Prims.int  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Absyn_Syntax.typ) = (fun c n t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(let _78_390 = (FStar_Util.first_N n lb)
in (match (_78_390) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _180_199 = (totalType_of_comp cp)
in (ll, _180_199))
end else begin
(let _180_200 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _180_200))
end
end))
end
| _78_392 -> begin
(let _78_393 = ()
in ([], t))
end)))

let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _180_205 = (zipUnequal ta tb)
in ((ha, hb))::_180_205)
end
| _78_407 -> begin
[]
end))

let mlTyIdentOfBinder : FStar_Absyn_Syntax.binder  ->  (Prims.string * Prims.int) = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

let extractCtor : FStar_Absyn_Syntax.binder Prims.list  ->  context  ->  inductiveConstructor  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlty Prims.list)) = (fun tyBinders c ctor -> (let _78_414 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_78_414) with
| (lb, tr) -> begin
(let _78_415 = ()
in (let lp = (FStar_List.zip tyBinders lb)
in (let newC = (let _180_215 = (FStar_List.map (fun _78_420 -> (match (_78_420) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _180_215 c))
in (let mlt = (let _180_216 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep c _180_216))
in (let tys = (let _180_217 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in (_180_217, mlt))
in (let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _180_220 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (let _180_219 = (let _180_218 = (argTypes mlt)
in ((lident2mlsymbol ctor.cname), _180_218))
in (_180_220, _180_219)))))))))
end)))

let rec firstNNats : Prims.int  ->  Prims.int Prims.list = (fun n -> if (0 < n) then begin
(let _180_223 = (firstNNats (n - 1))
in (n)::_180_223)
end else begin
[]
end)

let dummyIdent : Prims.int  ->  (Prims.string * Prims.int) = (fun n -> (let _180_227 = (let _180_226 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _180_226))
in (_180_227, 0)))

let dummyIndexIdents : Prims.int  ->  (Prims.string * Prims.int) Prims.list = (fun n -> (let _180_230 = (firstNNats n)
in (FStar_List.map dummyIdent _180_230)))

let extractInductive : context  ->  inductiveTypeFam  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c ind -> (let newContext = c
in (let nIndices = (numIndices ind.k ind.tyName.FStar_Ident.ident.FStar_Ident.idText)
in (let _78_434 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_78_434) with
| (nc, tyb) -> begin
(let mlbs = (let _180_236 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _180_235 = (dummyIndexIdents nIndices)
in (FStar_List.append _180_236 _180_235)))
in (let tbody = (match ((FStar_Util.find_opt (fun _78_1 -> (match (_78_1) with
| FStar_Absyn_Syntax.RecordType (_78_438) -> begin
true
end
| _78_441 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(let _78_445 = ()
in (let _78_450 = (FStar_List.hd tyb)
in (match (_78_450) with
| (_78_448, c_ty) -> begin
(let _78_451 = ()
in (let fields = (FStar_List.map2 (fun lid ty -> (lid.FStar_Ident.ident.FStar_Ident.idText, ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _78_457 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

let mfst = (fun x -> (FStar_List.map Prims.fst x))

let rec headBinders : context  ->  FStar_Absyn_Syntax.typ  ->  (context * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.typ) = (fun c t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _78_470 = (let _180_246 = (let _180_245 = (mfst bs)
in (extendContext c _180_245))
in (headBinders _180_246 t))
in (match (_78_470) with
| (c, rb, rresidualType) -> begin
(c, (FStar_List.append bs rb), rresidualType)
end))
end
| _78_472 -> begin
(c, [], t)
end)))

let extractTypeAbbrev : context  ->  typeAbbrev  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c tyab -> (let bs = tyab.abTyBinders
in (let t = tyab.abBody
in (let l = tyab.abTyName
in (let c = (let _180_251 = (mfst bs)
in (extendContext c _180_251))
in (let _78_482 = (headBinders c t)
in (match (_78_482) with
| (c, headBinders, residualType) -> begin
(let bs = (FStar_List.append bs headBinders)
in (let t = residualType
in (let mlt = (extractTyp c t)
in (let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tyDecBody = FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (let td = (let _180_252 = (FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _180_252, Some (tyDecBody)))
in (let c = (FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
in (c, td))))))))
end)))))))

let extractExn : context  ->  inductiveConstructor  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1) = (fun c exnConstr -> (let mlt = (extractTyp c exnConstr.ctype)
in (let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tys = ([], mlt)
in (let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (let ex_decl = (let _180_258 = (let _180_257 = (argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _180_257))
in FStar_Extraction_ML_Syntax.MLM_Exn (_180_258))
in (let _180_259 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (_180_259, ex_decl))))))))

let rec extractSigElt : context  ->  FStar_Absyn_Syntax.sigelt  ->  (context * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _78_502, t, quals, _78_506) -> begin
(let _78_511 = (extractTypeAbbrev c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_78_511) with
| (c, tds) -> begin
(let _180_264 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[]
end
in (c, _180_264))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, FStar_Absyn_Syntax.ExceptionConstructor::[], _78_516, _78_518) -> begin
(let _78_526 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_78_526) with
| (_78_522, _78_524, exConstrs) -> begin
(let _78_527 = ()
in (let _78_531 = (let _180_265 = (FStar_List.hd exConstrs)
in (extractExn c _180_265))
in (match (_78_531) with
| (c, exDecl) -> begin
(c, (exDecl)::[])
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _78_534, _78_536, _78_538) -> begin
(let _78_545 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_78_545) with
| (inds, abbs, _78_544) -> begin
(let _78_548 = (FStar_Util.fold_map extractInductive c inds)
in (match (_78_548) with
| (c, indDecls) -> begin
(let _78_551 = (FStar_Util.fold_map extractTypeAbbrev c abbs)
in (match (_78_551) with
| (c, tyAbDecls) -> begin
(c, (FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, k, _78_556, _78_558, quals, r) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_2 -> (match (_78_2) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _78_571 -> begin
false
end))))))) then begin
(let _78_575 = (FStar_Absyn_Util.kind_formals k)
in (match (_78_575) with
| (kbs, _78_574) -> begin
(let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((l, (FStar_List.append bs kbs), FStar_Absyn_Syntax.mk_Kind_type, FStar_Tc_Recheck.t_unit, quals, r))
in (extractSigElt c se))
end))
end else begin
(c, [])
end
end
| _78_578 -> begin
(c, [])
end))




