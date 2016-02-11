
open Prims
# 30 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let binderIsExp : FStar_Absyn_Syntax.binder  ->  Prims.bool = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))

# 32 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

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
| FStar_Absyn_Syntax.Kind_delayed (k, _78_14, _78_16) -> begin
(FStar_All.failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_78_20, k) -> begin
(argIsExp k typeName)
end
| _78_25 -> begin
(FStar_All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))

# 40 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let numIndices : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.nat = (fun k typeName -> (let _180_14 = (argIsExp k typeName)
in (FStar_List.length _180_14)))

# 44 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let mlty_of_isExp : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlty = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)

# 48 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

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
| Some (_78_38, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (let _78_43 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in delta_norm_eff))

# 61 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

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

# 70 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

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

# 86 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

type context =
FStar_Extraction_ML_Env.env

# 89 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extendContextWithRepAsTyVar : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either)  ->  context  ->  context = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_78_69)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false false)
end
| _78_73 -> begin
(FStar_All.failwith "Impossible case")
end))

# 99 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extendContextWithRepAsTyVars : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either) Prims.list  ->  context  ->  context = (fun b c -> (FStar_List.fold_right extendContextWithRepAsTyVar b c))

# 102 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

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

# 108 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extendContext : context  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  context = (fun c tyVars -> (FStar_List.fold_right (extendContextAsTyvar true) tyVars c))

# 115 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let isTypeScheme : FStar_Ident.lident  ->  context  ->  Prims.bool = (fun i c -> true)

# 118 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let preProcType : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun c ft -> (let ft = (FStar_Absyn_Util.compress_typ ft)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) c.FStar_Extraction_ML_Env.tcenv ft)))

# 122 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extractTyVar : context  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun c btv -> (FStar_Extraction_ML_Env.lookup_tyvar c btv))

# 136 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec extractTyp : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> (let ft = (preProcType c ft)
in (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| FStar_Absyn_Syntax.Typ_fun (bs, codomain) -> begin
(let _78_105 = (extractBindersTypes c bs)
in (match (_78_105) with
| (bts, newC) -> begin
(let _78_108 = (extractComp newC codomain)
in (match (_78_108) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _78_111) -> begin
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
| _78_128 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(let _78_136 = (extractBindersTypes c bs)
in (match (_78_136) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _78_139) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_78_145) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_78_148) -> begin
(FStar_All.failwith "expected the argument to be compressed")
end
| _78_151 -> begin
(FStar_All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg : context  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_78_157) -> begin
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
in (let _78_199 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_78_199) with
| (_78_197, missingArgs) -> begin
(let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _180_98 = (let _180_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in ((FStar_List.append mlargs argCompletion), _180_97))
in FStar_Extraction_ML_Syntax.MLTY_Named (_180_98)))
end)))))
end else begin
(FStar_All.failwith "this case was not anticipated")
end)
and extractBinderType : context  ->  FStar_Absyn_Syntax.binder  ->  (FStar_Extraction_ML_Syntax.mlty * context) = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _78_206) -> begin
(let _180_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _180_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in (_180_102, _180_101)))
end
| (FStar_Util.Inr (bvv), _78_211) -> begin
(let _180_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _180_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in (_180_104, _180_103)))
end))
and extractBindersTypes : context  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * context) = (fun c bs -> (let _180_110 = (FStar_List.fold_left (fun _78_217 b -> (match (_78_217) with
| (lt, cp) -> begin
(let _78_221 = (extractBinderType cp b)
in (match (_78_221) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _78_224 -> (match (_78_224) with
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

# 222 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let binderPPnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _78_239) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _78_244) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))

# 227 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let binderRealnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _78_250) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _78_255) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end))

# 233 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let mlsymbolOfLident : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

# 238 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

type inductiveConstructor =
{cname : FStar_Ident.lident; ctype : FStar_Absyn_Syntax.typ}

# 238 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let is_MkinductiveConstructor : inductiveConstructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveConstructor"))))

# 242 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

type inductiveTypeFam =
{tyName : FStar_Ident.lident; k : FStar_Absyn_Syntax.knd; tyBinders : FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : FStar_Absyn_Syntax.qualifier Prims.list}

# 242 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let is_MkinductiveTypeFam : inductiveTypeFam  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveTypeFam"))))

# 250 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

type typeAbbrev =
{abTyName : FStar_Ident.lident; abTyBinders : FStar_Absyn_Syntax.binders; abBody : FStar_Absyn_Syntax.typ}

# 250 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let is_MktypeAbbrev : typeAbbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MktypeAbbrev"))))

# 256 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let lookupDataConType : context  ->  FStar_Absyn_Syntax.sigelts  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun c sigb l -> (let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_78_278, tps, _78_281), quals, lids, _78_286) -> begin
if (l = l') then begin
(let t = (let _180_169 = (FStar_List.map (fun _78_292 -> (match (_78_292) with
| (x, _78_291) -> begin
(let _180_168 = (FStar_All.pipe_left (fun _180_167 -> Some (_180_167)) (FStar_Absyn_Syntax.Implicit (true)))
in (x, _180_168))
end)) tps)
in (FStar_Absyn_Util.close_typ _180_169 t))
in Some (t))
end else begin
None
end
end
| _78_295 -> begin
None
end)))
in (FStar_Util.must tr)))

# 268 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let parseInductiveConstructors : context  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelts  ->  inductiveConstructor Prims.list = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _180_177 = (lookupDataConType c sigb h)
in {cname = h; ctype = _180_177})) cnames))

# 273 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec parseInductiveTypesFromSigBundle : context  ->  FStar_Absyn_Syntax.sigelts  ->  (inductiveTypeFam Prims.list * typeAbbrev Prims.list * inductiveConstructor Prims.list) = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _78_309, constrs, qs, _78_313)::tlsig -> begin
(let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (let _78_321 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_78_321) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, _78_325, tc, quals, lids, _78_330)::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (let _78_335 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end else begin
([], [], [])
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _78_341, t, _78_344, _78_346)::tlsig -> begin
(let _78_353 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_78_353) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _180_183 = (let _180_182 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _180_182))
in (FStar_All.failwith _180_183))
end))

# 301 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _78_360, b) -> begin
(let _180_186 = (argTypes b)
in (a)::_180_186)
end
| _78_365 -> begin
[]
end))

# 306 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let lident2mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun l -> l.FStar_Ident.ident.FStar_Ident.idText)

# 308 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let totalType_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _78_371 -> begin
(FStar_All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

# 313 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let allBindersOfFuntype : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.binder Prims.list = (fun c t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _78_380 -> begin
[]
end)))

# 323 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let bindersOfFuntype : context  ->  Prims.int  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Absyn_Syntax.typ) = (fun c n t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(let _78_391 = (FStar_Util.first_N n lb)
in (match (_78_391) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _180_201 = (totalType_of_comp cp)
in (ll, _180_201))
end else begin
(let _180_202 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _180_202))
end
end))
end
| _78_393 -> begin
(let _78_394 = ()
in ([], t))
end)))

# 337 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _180_207 = (zipUnequal ta tb)
in ((ha, hb))::_180_207)
end
| _78_408 -> begin
[]
end))

# 342 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let mlTyIdentOfBinder : FStar_Absyn_Syntax.binder  ->  (Prims.string * Prims.int) = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

# 344 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extractCtor : FStar_Absyn_Syntax.binder Prims.list  ->  context  ->  inductiveConstructor  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlty Prims.list)) = (fun tyBinders c ctor -> (let _78_415 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_78_415) with
| (lb, tr) -> begin
(let _78_416 = ()
in (let lp = (FStar_List.zip tyBinders lb)
in (let newC = (let _180_217 = (FStar_List.map (fun _78_421 -> (match (_78_421) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _180_217 c))
in (let mlt = (let _180_218 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep c _180_218))
in (let tys = (let _180_219 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in (_180_219, mlt))
in (let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _180_222 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (let _180_221 = (let _180_220 = (argTypes mlt)
in ((lident2mlsymbol ctor.cname), _180_220))
in (_180_222, _180_221)))))))))
end)))

# 366 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec firstNNats : Prims.int  ->  Prims.int Prims.list = (fun n -> if (0 < n) then begin
(let _180_225 = (firstNNats (n - 1))
in (n)::_180_225)
end else begin
[]
end)

# 371 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let dummyIdent : Prims.int  ->  (Prims.string * Prims.int) = (fun n -> (let _180_229 = (let _180_228 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _180_228))
in (_180_229, 0)))

# 372 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let dummyIndexIdents : Prims.int  ->  (Prims.string * Prims.int) Prims.list = (fun n -> (let _180_232 = (firstNNats n)
in (FStar_List.map dummyIdent _180_232)))

# 374 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extractInductive : context  ->  inductiveTypeFam  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c ind -> (let newContext = c
in (let nIndices = (numIndices ind.k ind.tyName.FStar_Ident.ident.FStar_Ident.idText)
in (let _78_435 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_78_435) with
| (nc, tyb) -> begin
(let mlbs = (let _180_238 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _180_237 = (dummyIndexIdents nIndices)
in (FStar_List.append _180_238 _180_237)))
in (let tbody = (match ((FStar_Util.find_opt (fun _78_1 -> (match (_78_1) with
| FStar_Absyn_Syntax.RecordType (_78_439) -> begin
true
end
| _78_442 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(let _78_446 = ()
in (let _78_451 = (FStar_List.hd tyb)
in (match (_78_451) with
| (_78_449, c_ty) -> begin
(let _78_452 = ()
in (let fields = (FStar_List.map2 (fun lid ty -> (lid.FStar_Ident.ident.FStar_Ident.idText, ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _78_458 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

# 389 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let mfst = (fun x -> (FStar_List.map Prims.fst x))

# 395 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec headBinders : context  ->  FStar_Absyn_Syntax.typ  ->  (context * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.typ) = (fun c t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _78_471 = (let _180_248 = (let _180_247 = (mfst bs)
in (extendContext c _180_247))
in (headBinders _180_248 t))
in (match (_78_471) with
| (c, rb, rresidualType) -> begin
(c, (FStar_List.append bs rb), rresidualType)
end))
end
| _78_473 -> begin
(c, [], t)
end)))

# 403 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extractTypeAbbrev : FStar_Absyn_Syntax.qualifier Prims.list  ->  context  ->  typeAbbrev  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun quals c tyab -> (let bs = tyab.abTyBinders
in (let t = tyab.abBody
in (let l = tyab.abTyName
in (let c = (let _180_255 = (mfst bs)
in (extendContext c _180_255))
in (let _78_484 = (headBinders c t)
in (match (_78_484) with
| (c, headBinders, residualType) -> begin
(let bs = (FStar_List.append bs headBinders)
in (let t = residualType
in (let mlt = (extractTyp c t)
in (let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tyDecBody = FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (let td = (let _180_256 = (FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _180_256, Some (tyDecBody)))
in (let c = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_2 -> (match (_78_2) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.New) -> begin
true
end
| _78_495 -> begin
false
end)))) then begin
c
end else begin
(FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
end
in (c, td))))))))
end)))))))

# 426 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let extractExn : context  ->  inductiveConstructor  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1) = (fun c exnConstr -> (let mlt = (extractTyp c exnConstr.ctype)
in (let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tys = ([], mlt)
in (let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (let ex_decl = (let _180_263 = (let _180_262 = (argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _180_262))
in FStar_Extraction_ML_Syntax.MLM_Exn (_180_263))
in (let _180_264 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (_180_264, ex_decl))))))))

# 434 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let mlloc_of_range : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun r -> (let pos = (FStar_Range.start_of_range r)
in (let line = (FStar_Range.line_of_pos pos)
in (let _180_268 = (let _180_267 = (FStar_Range.file_of_range r)
in (line, _180_267))
in FStar_Extraction_ML_Syntax.MLM_Loc (_180_268)))))

# 441 "C:\\Users\\nswamy\\workspace\\FStar\\src\\extraction\\extracttyp.fs"

let rec extractSigElt : context  ->  FStar_Absyn_Syntax.sigelt  ->  (context * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _78_512, t, quals, range) -> begin
(let _78_520 = (extractTypeAbbrev quals c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_78_520) with
| (c, tds) -> begin
(let _180_274 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(let _180_273 = (mlloc_of_range range)
in (_180_273)::(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end
in (c, _180_274))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, FStar_Absyn_Syntax.ExceptionConstructor::[], _78_525, range) -> begin
(let _78_534 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_78_534) with
| (_78_530, _78_532, exConstrs) -> begin
(let _78_535 = ()
in (let _78_539 = (let _180_275 = (FStar_List.hd exConstrs)
in (extractExn c _180_275))
in (match (_78_539) with
| (c, exDecl) -> begin
(let _180_277 = (let _180_276 = (mlloc_of_range range)
in (_180_276)::(exDecl)::[])
in (c, _180_277))
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _78_542, _78_544, range) -> begin
(let _78_552 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_78_552) with
| (inds, abbs, _78_551) -> begin
(let _78_555 = (FStar_Util.fold_map extractInductive c inds)
in (match (_78_555) with
| (c, indDecls) -> begin
(let _78_558 = (FStar_Util.fold_map (extractTypeAbbrev []) c abbs)
in (match (_78_558) with
| (c, tyAbDecls) -> begin
(let _180_279 = (let _180_278 = (mlloc_of_range range)
in (_180_278)::(FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
in (c, _180_279))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, k, _78_563, _78_565, quals, r) -> begin
if (((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_3 -> (match (_78_3) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _78_578 -> begin
false
end))))))) then begin
(let _78_582 = (FStar_Absyn_Util.kind_formals k)
in (match (_78_582) with
| (kbs, _78_581) -> begin
(let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((l, (FStar_List.append bs kbs), FStar_Absyn_Syntax.mk_Kind_type, FStar_Tc_Recheck.t_unit, quals, r))
in (extractSigElt c se))
end))
end else begin
(c, [])
end
end
| _78_585 -> begin
(c, [])
end))




