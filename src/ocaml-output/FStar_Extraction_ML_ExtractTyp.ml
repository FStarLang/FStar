
open Prims
# 29 "FStar.Extraction.ML.ExtractTyp.fst"
let binderIsExp : FStar_Absyn_Syntax.binder  ->  Prims.bool = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))

# 31 "FStar.Extraction.ML.ExtractTyp.fst"
let rec argIsExp : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.bool Prims.list = (fun k typeName -> (match ((let _143_7 = (FStar_Absyn_Util.compress_kind k)
in _143_7.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _143_9 = (FStar_List.map binderIsExp bs)
in (let _143_8 = (argIsExp r typeName)
in (FStar_List.append _143_9 _143_8)))
end
| FStar_Absyn_Syntax.Kind_delayed (k, _64_14, _64_16) -> begin
(FStar_All.failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_64_20, k) -> begin
(argIsExp k typeName)
end
| _64_25 -> begin
(FStar_All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))

# 39 "FStar.Extraction.ML.ExtractTyp.fst"
let numIndices : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.nat = (fun k typeName -> (let _143_14 = (argIsExp k typeName)
in (FStar_List.length _143_14)))

# 42 "FStar.Extraction.ML.ExtractTyp.fst"
let mlty_of_isExp : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlty = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)

# 46 "FStar.Extraction.ML.ExtractTyp.fst"
let delta_norm_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 50 "FStar.Extraction.ML.ExtractTyp.fst"
let cache = (FStar_Util.smap_create 20)
in (
# 51 "FStar.Extraction.ML.ExtractTyp.fst"
let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(
# 55 "FStar.Extraction.ML.ExtractTyp.fst"
let res = (match ((FStar_Tc_Env.lookup_effect_abbrev g.FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some (_64_38, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (
# 58 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_43 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in delta_norm_eff))

# 60 "FStar.Extraction.ML.ExtractTyp.fst"
let translate_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g l -> (
# 63 "FStar.Extraction.ML.ExtractTyp.fst"
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

# 68 "FStar.Extraction.ML.ExtractTyp.fst"
let rec curry : FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun inp f out -> (match (inp) with
| [] -> begin
out
end
| h::[] -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _143_34 = (let _143_33 = (curry ((h2)::tl) f out)
in (h1, FStar_Extraction_ML_Syntax.E_PURE, _143_33))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_143_34))
end))

# 75 "FStar.Extraction.ML.ExtractTyp.fst"
type context =
FStar_Extraction_ML_Env.env

# 87 "FStar.Extraction.ML.ExtractTyp.fst"
let extendContextWithRepAsTyVar : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either)  ->  context  ->  context = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_64_69)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false false)
end
| _64_73 -> begin
(FStar_All.failwith "Impossible case")
end))

# 97 "FStar.Extraction.ML.ExtractTyp.fst"
let extendContextWithRepAsTyVars : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either) Prims.list  ->  context  ->  context = (fun b c -> (FStar_List.fold_right extendContextWithRepAsTyVar b c))

# 101 "FStar.Extraction.ML.ExtractTyp.fst"
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

# 107 "FStar.Extraction.ML.ExtractTyp.fst"
let extendContext : context  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  context = (fun c tyVars -> (FStar_List.fold_right (extendContextAsTyvar true) tyVars c))

# 110 "FStar.Extraction.ML.ExtractTyp.fst"
let isTypeScheme : FStar_Ident.lident  ->  context  ->  Prims.bool = (fun i c -> true)

# 116 "FStar.Extraction.ML.ExtractTyp.fst"
let preProcType : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun c ft -> (
# 120 "FStar.Extraction.ML.ExtractTyp.fst"
let ft = (FStar_Absyn_Util.compress_typ ft)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) c.FStar_Extraction_ML_Env.tcenv ft)))

# 121 "FStar.Extraction.ML.ExtractTyp.fst"
let extractTyVar : context  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun c btv -> (FStar_Extraction_ML_Env.lookup_tyvar c btv))

# 123 "FStar.Extraction.ML.ExtractTyp.fst"
let rec extractTyp : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> (
# 138 "FStar.Extraction.ML.ExtractTyp.fst"
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
# 146 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_105 = (extractBindersTypes c bs)
in (match (_64_105) with
| (bts, newC) -> begin
(
# 147 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_108 = (extractComp newC codomain)
in (match (_64_108) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _64_111) -> begin
(extractTyp c bv.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_app (ty, arrgs) -> begin
(
# 155 "FStar.Extraction.ML.ExtractTyp.fst"
let ty = (preProcType c ty)
in (
# 156 "FStar.Extraction.ML.ExtractTyp.fst"
let res = (match (ty.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| FStar_Absyn_Syntax.Typ_app (tyin, argsin) -> begin
(let _143_86 = (FStar_Extraction_ML_Util.mkTypApp tyin (FStar_List.append argsin arrgs) ty)
in (extractTyp c _143_86))
end
| _64_128 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(
# 165 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_136 = (extractBindersTypes c bs)
in (match (_64_136) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _64_139) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_64_145) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_64_148) -> begin
(FStar_All.failwith "expected the argument to be compressed")
end
| _64_151 -> begin
(FStar_All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg : context  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_64_157) -> begin
FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta : context  ->  FStar_Absyn_Syntax.meta_t  ->  FStar_Extraction_ML_Syntax.mlty = (fun c mt -> (match (mt) with
| (FStar_Absyn_Syntax.Meta_pattern (t, _)) | (FStar_Absyn_Syntax.Meta_named (t, _)) | (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _)) | (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _)) | (FStar_Absyn_Syntax.Meta_slack_formula (t, _, _)) -> begin
(extractTyp c t)
end))
and extractTyConstApp : context  ->  FStar_Absyn_Syntax.ftvar  ->  FStar_Absyn_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ftv ags -> if (isTypeScheme ftv.FStar_Absyn_Syntax.v c) then begin
(
# 193 "FStar.Extraction.ML.ExtractTyp.fst"
let mlargs = (FStar_List.map (getTypeFromArg c) ags)
in (
# 194 "FStar.Extraction.ML.ExtractTyp.fst"
let k = ftv.FStar_Absyn_Syntax.sort
in (
# 195 "FStar.Extraction.ML.ExtractTyp.fst"
let ar = (argIsExp k ftv.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (
# 197 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_199 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_64_199) with
| (_64_197, missingArgs) -> begin
(
# 198 "FStar.Extraction.ML.ExtractTyp.fst"
let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _143_98 = (let _143_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in ((FStar_List.append mlargs argCompletion), _143_97))
in FStar_Extraction_ML_Syntax.MLTY_Named (_143_98)))
end)))))
end else begin
(FStar_All.failwith "this case was not anticipated")
end)
and extractBinderType : context  ->  FStar_Absyn_Syntax.binder  ->  (FStar_Extraction_ML_Syntax.mlty * context) = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _64_206) -> begin
(let _143_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _143_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in (_143_102, _143_101)))
end
| (FStar_Util.Inr (bvv), _64_211) -> begin
(let _143_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _143_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in (_143_104, _143_103)))
end))
and extractBindersTypes : context  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * context) = (fun c bs -> (let _143_110 = (FStar_List.fold_left (fun _64_217 b -> (match (_64_217) with
| (lt, cp) -> begin
(
# 213 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_221 = (extractBinderType cp b)
in (match (_64_221) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _64_224 -> (match (_64_224) with
| (x, c) -> begin
((FStar_List.rev x), c)
end)) _143_110)))
and extractKind : context  ->  FStar_Absyn_Syntax.knd  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> FStar_Extraction_ML_Env.erasedContent)
and extractComp : context  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (extractComp' c ft.FStar_Absyn_Syntax.n))
and extractComp' : context  ->  FStar_Absyn_Syntax.comp'  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (match (ft) with
| FStar_Absyn_Syntax.Total (ty) -> begin
(let _143_117 = (extractTyp c ty)
in (_143_117, FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Absyn_Syntax.Comp (cm) -> begin
(let _143_119 = (extractTyp c cm.FStar_Absyn_Syntax.result_typ)
in (let _143_118 = (translate_eff c cm.FStar_Absyn_Syntax.effect_name)
in (_143_119, _143_118)))
end))

# 220 "FStar.Extraction.ML.ExtractTyp.fst"
let binderPPnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _64_239) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _64_244) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))

# 226 "FStar.Extraction.ML.ExtractTyp.fst"
let binderRealnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _64_250) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _64_255) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end))

# 231 "FStar.Extraction.ML.ExtractTyp.fst"
let mlsymbolOfLident : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)

# 235 "FStar.Extraction.ML.ExtractTyp.fst"
type inductiveConstructor =
{cname : FStar_Ident.lident; ctype : FStar_Absyn_Syntax.typ}

# 239 "FStar.Extraction.ML.ExtractTyp.fst"
let is_MkinductiveConstructor : inductiveConstructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveConstructor"))))

# 242 "FStar.Extraction.ML.ExtractTyp.fst"
type inductiveTypeFam =
{tyName : FStar_Ident.lident; k : FStar_Absyn_Syntax.knd; tyBinders : FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : FStar_Absyn_Syntax.qualifier Prims.list}

# 243 "FStar.Extraction.ML.ExtractTyp.fst"
let is_MkinductiveTypeFam : inductiveTypeFam  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveTypeFam"))))

# 249 "FStar.Extraction.ML.ExtractTyp.fst"
type typeAbbrev =
{abTyName : FStar_Ident.lident; abTyBinders : FStar_Absyn_Syntax.binders; abBody : FStar_Absyn_Syntax.typ}

# 251 "FStar.Extraction.ML.ExtractTyp.fst"
let is_MktypeAbbrev : typeAbbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MktypeAbbrev"))))

# 255 "FStar.Extraction.ML.ExtractTyp.fst"
let lookupDataConType : context  ->  FStar_Absyn_Syntax.sigelts  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun c sigb l -> (
# 258 "FStar.Extraction.ML.ExtractTyp.fst"
let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_64_278, tps, _64_281), quals, lids, _64_286) -> begin
if (l = l') then begin
(
# 263 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (let _143_169 = (FStar_List.map (fun _64_292 -> (match (_64_292) with
| (x, _64_291) -> begin
(let _143_168 = (FStar_All.pipe_left (fun _143_167 -> Some (_143_167)) (FStar_Absyn_Syntax.Implicit (true)))
in (x, _143_168))
end)) tps)
in (FStar_Absyn_Util.close_typ _143_169 t))
in Some (t))
end else begin
None
end
end
| _64_295 -> begin
None
end)))
in (FStar_Util.must tr)))

# 267 "FStar.Extraction.ML.ExtractTyp.fst"
let parseInductiveConstructors : context  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelts  ->  inductiveConstructor Prims.list = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _143_177 = (lookupDataConType c sigb h)
in {cname = h; ctype = _143_177})) cnames))

# 271 "FStar.Extraction.ML.ExtractTyp.fst"
let rec parseInductiveTypesFromSigBundle : context  ->  FStar_Absyn_Syntax.sigelts  ->  (inductiveTypeFam Prims.list * typeAbbrev Prims.list * inductiveConstructor Prims.list) = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _64_309, constrs, qs, _64_313)::tlsig -> begin
(
# 282 "FStar.Extraction.ML.ExtractTyp.fst"
let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (
# 283 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_321 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_64_321) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, _64_325, tc, quals, lids, _64_330)::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(
# 288 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (
# 289 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_335 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end else begin
([], [], [])
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _64_341, t, _64_344, _64_346)::tlsig -> begin
(
# 294 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_353 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_64_353) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _143_183 = (let _143_182 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _143_182))
in (FStar_All.failwith _143_183))
end))

# 297 "FStar.Extraction.ML.ExtractTyp.fst"
let lident2mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun l -> l.FStar_Ident.ident.FStar_Ident.idText)

# 301 "FStar.Extraction.ML.ExtractTyp.fst"
let totalType_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _64_362 -> begin
(FStar_All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

# 306 "FStar.Extraction.ML.ExtractTyp.fst"
let allBindersOfFuntype : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.binder Prims.list = (fun c t -> (
# 309 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _64_371 -> begin
[]
end)))

# 312 "FStar.Extraction.ML.ExtractTyp.fst"
let bindersOfFuntype : context  ->  Prims.int  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Absyn_Syntax.typ) = (fun c n t -> (
# 319 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(
# 321 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_382 = (FStar_Util.first_N n lb)
in (match (_64_382) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _143_198 = (totalType_of_comp cp)
in (ll, _143_198))
end else begin
(let _143_199 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _143_199))
end
end))
end
| _64_384 -> begin
(
# 328 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_385 = ()
in ([], t))
end)))

# 328 "FStar.Extraction.ML.ExtractTyp.fst"
let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _143_204 = (zipUnequal ta tb)
in ((ha, hb))::_143_204)
end
| _64_399 -> begin
[]
end))

# 335 "FStar.Extraction.ML.ExtractTyp.fst"
let mlTyIdentOfBinder : FStar_Absyn_Syntax.binder  ->  (Prims.string * Prims.int) = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

# 337 "FStar.Extraction.ML.ExtractTyp.fst"
let extractCtor : FStar_Absyn_Syntax.binder Prims.list  ->  context  ->  inductiveConstructor  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlty Prims.list)) = (fun tyBinders c ctor -> (
# 340 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_406 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_64_406) with
| (lb, tr) -> begin
(
# 341 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_407 = ()
in (
# 342 "FStar.Extraction.ML.ExtractTyp.fst"
let lp = (FStar_List.zip tyBinders lb)
in (
# 344 "FStar.Extraction.ML.ExtractTyp.fst"
let newC = (let _143_214 = (FStar_List.map (fun _64_412 -> (match (_64_412) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _143_214 c))
in (
# 345 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (let _143_215 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) _143_215))
in (
# 346 "FStar.Extraction.ML.ExtractTyp.fst"
let tys = (let _143_216 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in (_143_216, mlt))
in (
# 347 "FStar.Extraction.ML.ExtractTyp.fst"
let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _143_219 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (let _143_218 = (let _143_217 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident2mlsymbol ctor.cname), _143_217))
in (_143_219, _143_218)))))))))
end)))

# 351 "FStar.Extraction.ML.ExtractTyp.fst"
let rec firstNNats : Prims.int  ->  Prims.int Prims.list = (fun n -> if (0 < n) then begin
(let _143_222 = (firstNNats (n - 1))
in (n)::_143_222)
end else begin
[]
end)

# 364 "FStar.Extraction.ML.ExtractTyp.fst"
let dummyIdent : Prims.int  ->  (Prims.string * Prims.int) = (fun n -> (let _143_226 = (let _143_225 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _143_225))
in (_143_226, 0)))

# 366 "FStar.Extraction.ML.ExtractTyp.fst"
let dummyIndexIdents : Prims.int  ->  (Prims.string * Prims.int) Prims.list = (fun n -> (let _143_229 = (firstNNats n)
in (FStar_List.map dummyIdent _143_229)))

# 367 "FStar.Extraction.ML.ExtractTyp.fst"
let extractInductive : context  ->  inductiveTypeFam  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c ind -> (
# 370 "FStar.Extraction.ML.ExtractTyp.fst"
let newContext = c
in (
# 371 "FStar.Extraction.ML.ExtractTyp.fst"
let nIndices = (numIndices ind.k ind.tyName.FStar_Ident.ident.FStar_Ident.idText)
in (
# 372 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_426 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_64_426) with
| (nc, tyb) -> begin
(
# 373 "FStar.Extraction.ML.ExtractTyp.fst"
let mlbs = (let _143_235 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _143_234 = (dummyIndexIdents nIndices)
in (FStar_List.append _143_235 _143_234)))
in (
# 374 "FStar.Extraction.ML.ExtractTyp.fst"
let tbody = (match ((FStar_Util.find_opt (fun _64_1 -> (match (_64_1) with
| FStar_Absyn_Syntax.RecordType (_64_430) -> begin
true
end
| _64_433 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(
# 376 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_437 = ()
in (
# 377 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_442 = (FStar_List.hd tyb)
in (match (_64_442) with
| (_64_440, c_ty) -> begin
(
# 378 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_443 = ()
in (
# 379 "FStar.Extraction.ML.ExtractTyp.fst"
let fields = (FStar_List.map2 (fun lid ty -> (lid.FStar_Ident.ident.FStar_Ident.idText, ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _64_449 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

# 382 "FStar.Extraction.ML.ExtractTyp.fst"
let mfst = (fun x -> (FStar_List.map Prims.fst x))

# 384 "FStar.Extraction.ML.ExtractTyp.fst"
let rec headBinders : context  ->  FStar_Absyn_Syntax.typ  ->  (context * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.typ) = (fun c t -> (
# 391 "FStar.Extraction.ML.ExtractTyp.fst"
let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(
# 393 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_462 = (let _143_245 = (let _143_244 = (mfst bs)
in (extendContext c _143_244))
in (headBinders _143_245 t))
in (match (_64_462) with
| (c, rb, rresidualType) -> begin
(c, (FStar_List.append bs rb), rresidualType)
end))
end
| _64_464 -> begin
(c, [], t)
end)))

# 395 "FStar.Extraction.ML.ExtractTyp.fst"
let extractTypeAbbrev : FStar_Absyn_Syntax.qualifier Prims.list  ->  context  ->  typeAbbrev  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun quals c tyab -> (
# 399 "FStar.Extraction.ML.ExtractTyp.fst"
let bs = tyab.abTyBinders
in (
# 400 "FStar.Extraction.ML.ExtractTyp.fst"
let t = tyab.abBody
in (
# 401 "FStar.Extraction.ML.ExtractTyp.fst"
let l = tyab.abTyName
in (
# 402 "FStar.Extraction.ML.ExtractTyp.fst"
let c = (let _143_252 = (mfst bs)
in (extendContext c _143_252))
in (
# 408 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_475 = (headBinders c t)
in (match (_64_475) with
| (c, headBinders, residualType) -> begin
(
# 409 "FStar.Extraction.ML.ExtractTyp.fst"
let bs = (FStar_List.append bs headBinders)
in (
# 410 "FStar.Extraction.ML.ExtractTyp.fst"
let t = residualType
in (
# 411 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (extractTyp c t)
in (
# 412 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) mlt)
in (
# 413 "FStar.Extraction.ML.ExtractTyp.fst"
let tyDecBody = FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (
# 415 "FStar.Extraction.ML.ExtractTyp.fst"
let td = (let _143_253 = (FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _143_253, Some (tyDecBody)))
in (
# 416 "FStar.Extraction.ML.ExtractTyp.fst"
let c = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_2 -> (match (_64_2) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.New) -> begin
true
end
| _64_486 -> begin
false
end)))) then begin
c
end else begin
(FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
end
in (c, td))))))))
end)))))))

# 419 "FStar.Extraction.ML.ExtractTyp.fst"
let extractExn : context  ->  inductiveConstructor  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1) = (fun c exnConstr -> (
# 422 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (extractTyp c exnConstr.ctype)
in (
# 423 "FStar.Extraction.ML.ExtractTyp.fst"
let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) mlt)
in (
# 424 "FStar.Extraction.ML.ExtractTyp.fst"
let tys = ([], mlt)
in (
# 425 "FStar.Extraction.ML.ExtractTyp.fst"
let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (
# 426 "FStar.Extraction.ML.ExtractTyp.fst"
let ex_decl = (let _143_260 = (let _143_259 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _143_259))
in FStar_Extraction_ML_Syntax.MLM_Exn (_143_260))
in (let _143_261 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (_143_261, ex_decl))))))))

# 427 "FStar.Extraction.ML.ExtractTyp.fst"
let rec extractSigElt : context  ->  FStar_Absyn_Syntax.sigelt  ->  (context * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _64_500, t, quals, range) -> begin
(
# 434 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_508 = (extractTypeAbbrev quals c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_64_508) with
| (c, tds) -> begin
(let _143_268 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(let _143_267 = (let _143_266 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_143_266))
in (_143_267)::(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end
in (c, _143_268))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, FStar_Absyn_Syntax.ExceptionConstructor::[], _64_513, range) -> begin
(
# 438 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_522 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_64_522) with
| (_64_518, _64_520, exConstrs) -> begin
(
# 439 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_523 = ()
in (
# 440 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_527 = (let _143_269 = (FStar_List.hd exConstrs)
in (extractExn c _143_269))
in (match (_64_527) with
| (c, exDecl) -> begin
(let _143_272 = (let _143_271 = (let _143_270 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_143_270))
in (_143_271)::(exDecl)::[])
in (c, _143_272))
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _64_530, _64_532, range) -> begin
(
# 445 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_540 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_64_540) with
| (inds, abbs, _64_539) -> begin
(
# 446 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_543 = (FStar_Util.fold_map extractInductive c inds)
in (match (_64_543) with
| (c, indDecls) -> begin
(
# 447 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_546 = (FStar_Util.fold_map (extractTypeAbbrev []) c abbs)
in (match (_64_546) with
| (c, tyAbDecls) -> begin
(let _143_275 = (let _143_274 = (let _143_273 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_143_273))
in (_143_274)::(FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
in (c, _143_275))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, k, _64_551, _64_553, quals, r) -> begin
if (((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_3 -> (match (_64_3) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _64_566 -> begin
false
end))))))) then begin
(
# 455 "FStar.Extraction.ML.ExtractTyp.fst"
let _64_570 = (FStar_Absyn_Util.kind_formals k)
in (match (_64_570) with
| (kbs, _64_569) -> begin
(
# 456 "FStar.Extraction.ML.ExtractTyp.fst"
let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((l, (FStar_List.append bs kbs), FStar_Absyn_Syntax.mk_Kind_type, FStar_Tc_Recheck.t_unit, quals, r))
in (extractSigElt c se))
end))
end else begin
(c, [])
end
end
| _64_573 -> begin
(c, [])
end))




