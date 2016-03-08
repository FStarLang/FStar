
open Prims
# 30 "FStar.Extraction.ML.ExtractTyp.fst"
let binderIsExp : FStar_Absyn_Syntax.binder  ->  Prims.bool = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))

# 32 "FStar.Extraction.ML.ExtractTyp.fst"
let rec argIsExp : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.bool Prims.list = (fun k typeName -> (match ((let _142_7 = (FStar_Absyn_Util.compress_kind k)
in _142_7.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _142_9 = (FStar_List.map binderIsExp bs)
in (let _142_8 = (argIsExp r typeName)
in (FStar_List.append _142_9 _142_8)))
end
| FStar_Absyn_Syntax.Kind_delayed (k, _61_14, _61_16) -> begin
(FStar_All.failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_61_20, k) -> begin
(argIsExp k typeName)
end
| _61_25 -> begin
(FStar_All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))

# 40 "FStar.Extraction.ML.ExtractTyp.fst"
let numIndices : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.nat = (fun k typeName -> (let _142_14 = (argIsExp k typeName)
in (FStar_List.length _142_14)))

# 44 "FStar.Extraction.ML.ExtractTyp.fst"
let mlty_of_isExp : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlty = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)

# 48 "FStar.Extraction.ML.ExtractTyp.fst"
let delta_norm_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 49 "FStar.Extraction.ML.ExtractTyp.fst"
let cache = (FStar_Util.smap_create 20)
in (
# 50 "FStar.Extraction.ML.ExtractTyp.fst"
let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(
# 54 "FStar.Extraction.ML.ExtractTyp.fst"
let res = (match ((FStar_Tc_Env.lookup_effect_abbrev g.FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some (_61_38, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (
# 57 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_43 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in delta_norm_eff))

# 61 "FStar.Extraction.ML.ExtractTyp.fst"
let translate_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g l -> (
# 62 "FStar.Extraction.ML.ExtractTyp.fst"
let l = (delta_norm_eff g l)
in if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))

# 70 "FStar.Extraction.ML.ExtractTyp.fst"
let rec curry : FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun inp f out -> (match (inp) with
| [] -> begin
out
end
| h::[] -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _142_34 = (let _142_33 = (curry ((h2)::tl) f out)
in (h1, FStar_Extraction_ML_Syntax.E_PURE, _142_33))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_142_34))
end))

# 86 "FStar.Extraction.ML.ExtractTyp.fst"
type context =
FStar_Extraction_ML_Env.env

# 89 "FStar.Extraction.ML.ExtractTyp.fst"
let extendContextWithRepAsTyVar : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either)  ->  context  ->  context = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_61_69)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false false)
end
| _61_73 -> begin
(FStar_All.failwith "Impossible case")
end))

# 99 "FStar.Extraction.ML.ExtractTyp.fst"
let extendContextWithRepAsTyVars : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either) Prims.list  ->  context  ->  context = (fun b c -> (FStar_List.fold_right extendContextWithRepAsTyVar b c))

# 102 "FStar.Extraction.ML.ExtractTyp.fst"
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

# 108 "FStar.Extraction.ML.ExtractTyp.fst"
let extendContext : context  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  context = (fun c tyVars -> (FStar_List.fold_right (extendContextAsTyvar true) tyVars c))

# 115 "FStar.Extraction.ML.ExtractTyp.fst"
let isTypeScheme : FStar_Ident.lident  ->  context  ->  Prims.bool = (fun i c -> true)

# 118 "FStar.Extraction.ML.ExtractTyp.fst"
let preProcType : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun c ft -> (
# 119 "FStar.Extraction.ML.ExtractTyp.fst"
let ft = (FStar_Absyn_Util.compress_typ ft)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) c.FStar_Extraction_ML_Env.tcenv ft)))

# 122 "FStar.Extraction.ML.ExtractTyp.fst"
let extractTyVar : context  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun c btv -> (FStar_Extraction_ML_Env.lookup_tyvar c btv))

# 136 "FStar.Extraction.ML.ExtractTyp.fst"
let rec extractTyp : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> (
# 137 "FStar.Extraction.ML.ExtractTyp.fst"
let ft = (preProcType c ft)
in (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| FStar_Absyn_Syntax.Typ_fun (bs, codomain) -> begin
(
# 145 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_105 = (extractBindersTypes c bs)
in (match (_61_105) with
| (bts, newC) -> begin
(
# 146 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_108 = (extractComp newC codomain)
in (match (_61_108) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _61_111) -> begin
(extractTyp c bv.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_app (ty, arrgs) -> begin
(
# 154 "FStar.Extraction.ML.ExtractTyp.fst"
let ty = (preProcType c ty)
in (
# 155 "FStar.Extraction.ML.ExtractTyp.fst"
let res = (match (ty.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| FStar_Absyn_Syntax.Typ_app (tyin, argsin) -> begin
(let _142_86 = (FStar_Extraction_ML_Util.mkTypApp tyin (FStar_List.append argsin arrgs) ty)
in (extractTyp c _142_86))
end
| _61_128 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(
# 164 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_136 = (extractBindersTypes c bs)
in (match (_61_136) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _61_139) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_61_145) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_61_148) -> begin
(FStar_All.failwith "expected the argument to be compressed")
end
| _61_151 -> begin
(FStar_All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg : context  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_61_157) -> begin
FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta : context  ->  FStar_Absyn_Syntax.meta_t  ->  FStar_Extraction_ML_Syntax.mlty = (fun c mt -> (match (mt) with
| (FStar_Absyn_Syntax.Meta_pattern (t, _)) | (FStar_Absyn_Syntax.Meta_named (t, _)) | (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _)) | (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _)) | (FStar_Absyn_Syntax.Meta_slack_formula (t, _, _)) -> begin
(extractTyp c t)
end))
and extractTyConstApp : context  ->  FStar_Absyn_Syntax.ftvar  ->  FStar_Absyn_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ftv ags -> if (isTypeScheme ftv.FStar_Absyn_Syntax.v c) then begin
(
# 192 "FStar.Extraction.ML.ExtractTyp.fst"
let mlargs = (FStar_List.map (getTypeFromArg c) ags)
in (
# 193 "FStar.Extraction.ML.ExtractTyp.fst"
let k = ftv.FStar_Absyn_Syntax.sort
in (
# 194 "FStar.Extraction.ML.ExtractTyp.fst"
let ar = (argIsExp k ftv.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (
# 196 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_199 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_61_199) with
| (_61_197, missingArgs) -> begin
(
# 197 "FStar.Extraction.ML.ExtractTyp.fst"
let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _142_98 = (let _142_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in ((FStar_List.append mlargs argCompletion), _142_97))
in FStar_Extraction_ML_Syntax.MLTY_Named (_142_98)))
end)))))
end else begin
(FStar_All.failwith "this case was not anticipated")
end)
and extractBinderType : context  ->  FStar_Absyn_Syntax.binder  ->  (FStar_Extraction_ML_Syntax.mlty * context) = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _61_206) -> begin
(let _142_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _142_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in (_142_102, _142_101)))
end
| (FStar_Util.Inr (bvv), _61_211) -> begin
(let _142_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _142_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in (_142_104, _142_103)))
end))
and extractBindersTypes : context  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * context) = (fun c bs -> (let _142_110 = (FStar_List.fold_left (fun _61_217 b -> (match (_61_217) with
| (lt, cp) -> begin
(
# 212 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_221 = (extractBinderType cp b)
in (match (_61_221) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _61_224 -> (match (_61_224) with
| (x, c) -> begin
((FStar_List.rev x), c)
end)) _142_110)))
and extractKind : context  ->  FStar_Absyn_Syntax.knd  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> FStar_Extraction_ML_Env.erasedContent)
and extractComp : context  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (extractComp' c ft.FStar_Absyn_Syntax.n))
and extractComp' : context  ->  FStar_Absyn_Syntax.comp'  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (match (ft) with
| FStar_Absyn_Syntax.Total (ty) -> begin
(let _142_117 = (extractTyp c ty)
in (_142_117, FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Absyn_Syntax.Comp (cm) -> begin
(let _142_119 = (extractTyp c cm.FStar_Absyn_Syntax.result_typ)
in (let _142_118 = (translate_eff c cm.FStar_Absyn_Syntax.effect_name)
in (_142_119, _142_118)))
end))

# 222 "FStar.Extraction.ML.ExtractTyp.fst"
let binderPPnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _61_239) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _61_244) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))

# 227 "FStar.Extraction.ML.ExtractTyp.fst"
let binderRealnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _61_250) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _61_255) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end))

# 233 "FStar.Extraction.ML.ExtractTyp.fst"
let mlsymbolOfLident : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

# 238 "FStar.Extraction.ML.ExtractTyp.fst"
type inductiveConstructor =
{cname : FStar_Ident.lident; ctype : FStar_Absyn_Syntax.typ}

# 238 "FStar.Extraction.ML.ExtractTyp.fst"
let is_MkinductiveConstructor : inductiveConstructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveConstructor"))))

# 242 "FStar.Extraction.ML.ExtractTyp.fst"
type inductiveTypeFam =
{tyName : FStar_Ident.lident; k : FStar_Absyn_Syntax.knd; tyBinders : FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : FStar_Absyn_Syntax.qualifier Prims.list}

# 242 "FStar.Extraction.ML.ExtractTyp.fst"
let is_MkinductiveTypeFam : inductiveTypeFam  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveTypeFam"))))

# 250 "FStar.Extraction.ML.ExtractTyp.fst"
type typeAbbrev =
{abTyName : FStar_Ident.lident; abTyBinders : FStar_Absyn_Syntax.binders; abBody : FStar_Absyn_Syntax.typ}

# 250 "FStar.Extraction.ML.ExtractTyp.fst"
let is_MktypeAbbrev : typeAbbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MktypeAbbrev"))))

# 256 "FStar.Extraction.ML.ExtractTyp.fst"
let lookupDataConType : context  ->  FStar_Absyn_Syntax.sigelts  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun c sigb l -> (
# 257 "FStar.Extraction.ML.ExtractTyp.fst"
let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_61_278, tps, _61_281), quals, lids, _61_286) -> begin
if (l = l') then begin
(
# 262 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (let _142_169 = (FStar_List.map (fun _61_292 -> (match (_61_292) with
| (x, _61_291) -> begin
(let _142_168 = (FStar_All.pipe_left (fun _142_167 -> Some (_142_167)) (FStar_Absyn_Syntax.Implicit (true)))
in (x, _142_168))
end)) tps)
in (FStar_Absyn_Util.close_typ _142_169 t))
in Some (t))
end else begin
None
end
end
| _61_295 -> begin
None
end)))
in (FStar_Util.must tr)))

# 268 "FStar.Extraction.ML.ExtractTyp.fst"
let parseInductiveConstructors : context  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelts  ->  inductiveConstructor Prims.list = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _142_177 = (lookupDataConType c sigb h)
in {cname = h; ctype = _142_177})) cnames))

# 273 "FStar.Extraction.ML.ExtractTyp.fst"
let rec parseInductiveTypesFromSigBundle : context  ->  FStar_Absyn_Syntax.sigelts  ->  (inductiveTypeFam Prims.list * typeAbbrev Prims.list * inductiveConstructor Prims.list) = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _61_309, constrs, qs, _61_313)::tlsig -> begin
(
# 281 "FStar.Extraction.ML.ExtractTyp.fst"
let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (
# 282 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_321 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_61_321) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, _61_325, tc, quals, lids, _61_330)::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(
# 287 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (
# 288 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_335 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end else begin
([], [], [])
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _61_341, t, _61_344, _61_346)::tlsig -> begin
(
# 293 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_353 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_61_353) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _142_183 = (let _142_182 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _142_182))
in (FStar_All.failwith _142_183))
end))

# 301 "FStar.Extraction.ML.ExtractTyp.fst"
let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _61_360, b) -> begin
(let _142_186 = (argTypes b)
in (a)::_142_186)
end
| _61_365 -> begin
[]
end))

# 306 "FStar.Extraction.ML.ExtractTyp.fst"
let lident2mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun l -> l.FStar_Ident.ident.FStar_Ident.idText)

# 308 "FStar.Extraction.ML.ExtractTyp.fst"
let totalType_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _61_371 -> begin
(FStar_All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

# 313 "FStar.Extraction.ML.ExtractTyp.fst"
let allBindersOfFuntype : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.binder Prims.list = (fun c t -> (
# 314 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _61_380 -> begin
[]
end)))

# 323 "FStar.Extraction.ML.ExtractTyp.fst"
let bindersOfFuntype : context  ->  Prims.int  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Absyn_Syntax.typ) = (fun c n t -> (
# 324 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(
# 326 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_391 = (FStar_Util.first_N n lb)
in (match (_61_391) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _142_201 = (totalType_of_comp cp)
in (ll, _142_201))
end else begin
(let _142_202 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _142_202))
end
end))
end
| _61_393 -> begin
(
# 333 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_394 = ()
in ([], t))
end)))

# 337 "FStar.Extraction.ML.ExtractTyp.fst"
let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _142_207 = (zipUnequal ta tb)
in ((ha, hb))::_142_207)
end
| _61_408 -> begin
[]
end))

# 342 "FStar.Extraction.ML.ExtractTyp.fst"
let mlTyIdentOfBinder : FStar_Absyn_Syntax.binder  ->  (Prims.string * Prims.int) = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

# 344 "FStar.Extraction.ML.ExtractTyp.fst"
let extractCtor : FStar_Absyn_Syntax.binder Prims.list  ->  context  ->  inductiveConstructor  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlty Prims.list)) = (fun tyBinders c ctor -> (
# 345 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_415 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_61_415) with
| (lb, tr) -> begin
(
# 346 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_416 = ()
in (
# 347 "FStar.Extraction.ML.ExtractTyp.fst"
let lp = (FStar_List.zip tyBinders lb)
in (
# 349 "FStar.Extraction.ML.ExtractTyp.fst"
let newC = (let _142_217 = (FStar_List.map (fun _61_421 -> (match (_61_421) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _142_217 c))
in (
# 350 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (let _142_218 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep c _142_218))
in (
# 351 "FStar.Extraction.ML.ExtractTyp.fst"
let tys = (let _142_219 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in (_142_219, mlt))
in (
# 352 "FStar.Extraction.ML.ExtractTyp.fst"
let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _142_222 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (let _142_221 = (let _142_220 = (argTypes mlt)
in ((lident2mlsymbol ctor.cname), _142_220))
in (_142_222, _142_221)))))))))
end)))

# 366 "FStar.Extraction.ML.ExtractTyp.fst"
let rec firstNNats : Prims.int  ->  Prims.int Prims.list = (fun n -> if (0 < n) then begin
(let _142_225 = (firstNNats (n - 1))
in (n)::_142_225)
end else begin
[]
end)

# 371 "FStar.Extraction.ML.ExtractTyp.fst"
let dummyIdent : Prims.int  ->  (Prims.string * Prims.int) = (fun n -> (let _142_229 = (let _142_228 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _142_228))
in (_142_229, 0)))

# 372 "FStar.Extraction.ML.ExtractTyp.fst"
let dummyIndexIdents : Prims.int  ->  (Prims.string * Prims.int) Prims.list = (fun n -> (let _142_232 = (firstNNats n)
in (FStar_List.map dummyIdent _142_232)))

# 374 "FStar.Extraction.ML.ExtractTyp.fst"
let extractInductive : context  ->  inductiveTypeFam  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c ind -> (
# 375 "FStar.Extraction.ML.ExtractTyp.fst"
let newContext = c
in (
# 376 "FStar.Extraction.ML.ExtractTyp.fst"
let nIndices = (numIndices ind.k ind.tyName.FStar_Ident.ident.FStar_Ident.idText)
in (
# 377 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_435 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_61_435) with
| (nc, tyb) -> begin
(
# 378 "FStar.Extraction.ML.ExtractTyp.fst"
let mlbs = (let _142_238 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _142_237 = (dummyIndexIdents nIndices)
in (FStar_List.append _142_238 _142_237)))
in (
# 379 "FStar.Extraction.ML.ExtractTyp.fst"
let tbody = (match ((FStar_Util.find_opt (fun _61_1 -> (match (_61_1) with
| FStar_Absyn_Syntax.RecordType (_61_439) -> begin
true
end
| _61_442 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(
# 381 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_446 = ()
in (
# 382 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_451 = (FStar_List.hd tyb)
in (match (_61_451) with
| (_61_449, c_ty) -> begin
(
# 383 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_452 = ()
in (
# 384 "FStar.Extraction.ML.ExtractTyp.fst"
let fields = (FStar_List.map2 (fun lid ty -> (lid.FStar_Ident.ident.FStar_Ident.idText, ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _61_458 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

# 389 "FStar.Extraction.ML.ExtractTyp.fst"
let mfst = (fun x -> (FStar_List.map Prims.fst x))

# 395 "FStar.Extraction.ML.ExtractTyp.fst"
let rec headBinders : context  ->  FStar_Absyn_Syntax.typ  ->  (context * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.typ) = (fun c t -> (
# 396 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(
# 398 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_471 = (let _142_248 = (let _142_247 = (mfst bs)
in (extendContext c _142_247))
in (headBinders _142_248 t))
in (match (_61_471) with
| (c, rb, rresidualType) -> begin
(c, (FStar_List.append bs rb), rresidualType)
end))
end
| _61_473 -> begin
(c, [], t)
end)))

# 403 "FStar.Extraction.ML.ExtractTyp.fst"
let extractTypeAbbrev : FStar_Absyn_Syntax.qualifier Prims.list  ->  context  ->  typeAbbrev  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun quals c tyab -> (
# 404 "FStar.Extraction.ML.ExtractTyp.fst"
let bs = tyab.abTyBinders
in (
# 405 "FStar.Extraction.ML.ExtractTyp.fst"
let t = tyab.abBody
in (
# 406 "FStar.Extraction.ML.ExtractTyp.fst"
let l = tyab.abTyName
in (
# 407 "FStar.Extraction.ML.ExtractTyp.fst"
let c = (let _142_255 = (mfst bs)
in (extendContext c _142_255))
in (
# 413 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_484 = (headBinders c t)
in (match (_61_484) with
| (c, headBinders, residualType) -> begin
(
# 414 "FStar.Extraction.ML.ExtractTyp.fst"
let bs = (FStar_List.append bs headBinders)
in (
# 415 "FStar.Extraction.ML.ExtractTyp.fst"
let t = residualType
in (
# 416 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (extractTyp c t)
in (
# 417 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (
# 418 "FStar.Extraction.ML.ExtractTyp.fst"
let tyDecBody = FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (
# 420 "FStar.Extraction.ML.ExtractTyp.fst"
let td = (let _142_256 = (FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _142_256, Some (tyDecBody)))
in (
# 421 "FStar.Extraction.ML.ExtractTyp.fst"
let c = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_2 -> (match (_61_2) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.New) -> begin
true
end
| _61_495 -> begin
false
end)))) then begin
c
end else begin
(FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
end
in (c, td))))))))
end)))))))

# 426 "FStar.Extraction.ML.ExtractTyp.fst"
let extractExn : context  ->  inductiveConstructor  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1) = (fun c exnConstr -> (
# 427 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (extractTyp c exnConstr.ctype)
in (
# 428 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (
# 429 "FStar.Extraction.ML.ExtractTyp.fst"
let tys = ([], mlt)
in (
# 430 "FStar.Extraction.ML.ExtractTyp.fst"
let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (
# 431 "FStar.Extraction.ML.ExtractTyp.fst"
let ex_decl = (let _142_263 = (let _142_262 = (argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _142_262))
in FStar_Extraction_ML_Syntax.MLM_Exn (_142_263))
in (let _142_264 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (_142_264, ex_decl))))))))

# 434 "FStar.Extraction.ML.ExtractTyp.fst"
let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (
# 435 "FStar.Extraction.ML.ExtractTyp.fst"
let pos = (FStar_Range.start_of_range r)
in (
# 436 "FStar.Extraction.ML.ExtractTyp.fst"
let line = (FStar_Range.line_of_pos pos)
in (let _142_267 = (FStar_Range.file_of_range r)
in (line, _142_267)))))

# 441 "FStar.Extraction.ML.ExtractTyp.fst"
let rec extractSigElt : context  ->  FStar_Absyn_Syntax.sigelt  ->  (context * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _61_512, t, quals, range) -> begin
(
# 444 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_520 = (extractTypeAbbrev quals c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_61_520) with
| (c, tds) -> begin
(let _142_274 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(let _142_273 = (let _142_272 = (mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_142_272))
in (_142_273)::(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end
in (c, _142_274))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, FStar_Absyn_Syntax.ExceptionConstructor::[], _61_525, range) -> begin
(
# 448 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_534 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_61_534) with
| (_61_530, _61_532, exConstrs) -> begin
(
# 449 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_535 = ()
in (
# 450 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_539 = (let _142_275 = (FStar_List.hd exConstrs)
in (extractExn c _142_275))
in (match (_61_539) with
| (c, exDecl) -> begin
(let _142_278 = (let _142_277 = (let _142_276 = (mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_142_276))
in (_142_277)::(exDecl)::[])
in (c, _142_278))
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _61_542, _61_544, range) -> begin
(
# 455 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_552 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_61_552) with
| (inds, abbs, _61_551) -> begin
(
# 456 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_555 = (FStar_Util.fold_map extractInductive c inds)
in (match (_61_555) with
| (c, indDecls) -> begin
(
# 457 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_558 = (FStar_Util.fold_map (extractTypeAbbrev []) c abbs)
in (match (_61_558) with
| (c, tyAbDecls) -> begin
(let _142_281 = (let _142_280 = (let _142_279 = (mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_142_279))
in (_142_280)::(FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
in (c, _142_281))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, k, _61_563, _61_565, quals, r) -> begin
if (((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_3 -> (match (_61_3) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _61_578 -> begin
false
end))))))) then begin
(
# 465 "FStar.Extraction.ML.ExtractTyp.fst"
let _61_582 = (FStar_Absyn_Util.kind_formals k)
in (match (_61_582) with
| (kbs, _61_581) -> begin
(
# 466 "FStar.Extraction.ML.ExtractTyp.fst"
let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((l, (FStar_List.append bs kbs), FStar_Absyn_Syntax.mk_Kind_type, FStar_Tc_Recheck.t_unit, quals, r))
in (extractSigElt c se))
end))
end else begin
(c, [])
end
end
| _61_585 -> begin
(c, [])
end))




