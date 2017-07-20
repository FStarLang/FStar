
open Prims

let binderIsExp : FStar_Absyn_Syntax.binder  ->  Prims.bool = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))


let rec argIsExp : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.bool Prims.list = (fun k typeName -> (match ((let _178_7 = (FStar_Absyn_Util.compress_kind k)
in _178_7.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _178_9 = (FStar_List.map binderIsExp bs)
in (let _178_8 = (argIsExp r typeName)
in (FStar_List.append _178_9 _178_8)))
end
| FStar_Absyn_Syntax.Kind_delayed (k, _79_15, _79_17) -> begin
(failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_79_21, k) -> begin
(argIsExp k typeName)
end
| _79_26 -> begin
(failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))


let numIndices : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.nat = (fun k typeName -> (let _178_14 = (argIsExp k typeName)
in (FStar_List.length _178_14)))


let mlty_of_isExp : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlty = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)


let delta_norm_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_Tc_Env.lookup_effect_abbrev g.FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some (_79_39, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (

let _79_44 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in delta_norm_eff))


let translate_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g l -> (

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


let rec curry : FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun inp f out -> (match (inp) with
| [] -> begin
out
end
| (h)::[] -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((h), (f), (out)))
end
| (h1)::(h2)::tl -> begin
(let _178_34 = (let _178_33 = (curry ((h2)::tl) f out)
in ((h1), (FStar_Extraction_ML_Syntax.E_PURE), (_178_33)))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_178_34))
end))


type context =
FStar_Extraction_ML_Env.env


let extendContextWithRepAsTyVar : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either)  ->  context  ->  context = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_79_70)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv (([]), (FStar_Extraction_ML_Env.erasedContent)) false false false)
end
| _79_74 -> begin
(failwith "Impossible case")
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
(FStar_Extraction_ML_Env.extend_bv c bv (([]), (FStar_Extraction_ML_Env.erasedContent)) false false false)
end))


let extendContext : context  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  context = (fun c tyVars -> (FStar_List.fold_right (extendContextAsTyvar true) tyVars c))


let isTypeScheme : FStar_Ident.lident  ->  context  ->  Prims.bool = (fun i c -> true)


let preProcType : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun c ft -> (

let ft = (FStar_Absyn_Util.compress_typ ft)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) c.FStar_Extraction_ML_Env.tcenv ft)))


let extractTyVar : context  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun c btv -> (FStar_Extraction_ML_Env.lookup_tyvar c btv))


let rec extractTyp : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> (

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

let _79_106 = (extractBindersTypes c bs)
in (match (_79_106) with
| (bts, newC) -> begin
(

let _79_109 = (extractComp newC codomain)
in (match (_79_109) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _79_112) -> begin
(extractTyp c bv.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_app (ty, arrgs) -> begin
(

let ty = (preProcType c ty)
in (

let res = (match (ty.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| FStar_Absyn_Syntax.Typ_app (tyin, argsin) -> begin
(let _178_86 = (FStar_Extraction_ML_Util.mkTypApp tyin (FStar_List.append argsin arrgs) ty)
in (extractTyp c _178_86))
end
| _79_129 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(

let _79_137 = (extractBindersTypes c bs)
in (match (_79_137) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _79_140) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_79_146) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_79_149) -> begin
(failwith "expected the argument to be compressed")
end
| _79_152 -> begin
(failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg : context  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_79_158) -> begin
FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta : context  ->  FStar_Absyn_Syntax.meta_t  ->  FStar_Extraction_ML_Syntax.mlty = (fun c mt -> (match (mt) with
| (FStar_Absyn_Syntax.Meta_pattern (t, _)) | (FStar_Absyn_Syntax.Meta_named (t, _)) | (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _)) | (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _)) | (FStar_Absyn_Syntax.Meta_slack_formula (t, _, _)) -> begin
(extractTyp c t)
end))
and extractTyConstApp : context  ->  FStar_Absyn_Syntax.ftvar  ->  FStar_Absyn_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ftv ags -> if (isTypeScheme ftv.FStar_Absyn_Syntax.v c) then begin
(

let mlargs = (FStar_List.map (getTypeFromArg c) ags)
in (

let k = ftv.FStar_Absyn_Syntax.sort
in (

let ar = (argIsExp k ftv.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (

let _79_200 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_79_200) with
| (_79_198, missingArgs) -> begin
(

let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _178_98 = (let _178_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in (((FStar_List.append mlargs argCompletion)), (_178_97)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_178_98)))
end)))))
end else begin
(failwith "this case was not anticipated")
end)
and extractBinderType : context  ->  FStar_Absyn_Syntax.binder  ->  (FStar_Extraction_ML_Syntax.mlty * context) = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _79_207) -> begin
(let _178_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _178_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in ((_178_102), (_178_101))))
end
| (FStar_Util.Inr (bvv), _79_212) -> begin
(let _178_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _178_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in ((_178_104), (_178_103))))
end))
and extractBindersTypes : context  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * context) = (fun c bs -> (let _178_110 = (FStar_List.fold_left (fun _79_218 b -> (match (_79_218) with
| (lt, cp) -> begin
(

let _79_222 = (extractBinderType cp b)
in (match (_79_222) with
| (nt, nc) -> begin
(((nt)::lt), (nc))
end))
end)) (([]), (c)) bs)
in ((fun _79_225 -> (match (_79_225) with
| (x, c) -> begin
(((FStar_List.rev x)), (c))
end)) _178_110)))
and extractKind : context  ->  FStar_Absyn_Syntax.knd  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> FStar_Extraction_ML_Env.erasedContent)
and extractComp : context  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (extractComp' c ft.FStar_Absyn_Syntax.n))
and extractComp' : context  ->  FStar_Absyn_Syntax.comp'  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (match (ft) with
| FStar_Absyn_Syntax.Total (ty) -> begin
(let _178_117 = (extractTyp c ty)
in ((_178_117), (FStar_Extraction_ML_Syntax.E_PURE)))
end
| FStar_Absyn_Syntax.Comp (cm) -> begin
(let _178_119 = (extractTyp c cm.FStar_Absyn_Syntax.result_typ)
in (let _178_118 = (translate_eff c cm.FStar_Absyn_Syntax.effect_name)
in ((_178_119), (_178_118))))
end))


let binderPPnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _79_240) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _79_245) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))


let binderRealnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _79_251) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _79_256) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end))


let mlsymbolOfLident : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


type inductiveConstructor =
{cname : FStar_Ident.lident; ctype : FStar_Absyn_Syntax.typ}


let is_MkinductiveConstructor : inductiveConstructor  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_MkinductiveConstructor"))))


type inductiveTypeFam =
{tyName : FStar_Ident.lident; k : FStar_Absyn_Syntax.knd; tyBinders : FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : FStar_Absyn_Syntax.qualifier Prims.list}


let is_MkinductiveTypeFam : inductiveTypeFam  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_MkinductiveTypeFam"))))


type typeAbbrev =
{abTyName : FStar_Ident.lident; abTyBinders : FStar_Absyn_Syntax.binders; abBody : FStar_Absyn_Syntax.typ}


let is_MktypeAbbrev : typeAbbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_MktypeAbbrev"))))


let lookupDataConType : context  ->  FStar_Absyn_Syntax.sigelts  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun c sigb l -> (

let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_79_279, tps, _79_282), quals, lids, _79_287) -> begin
if (l = l') then begin
(

let t = (let _178_169 = (FStar_List.map (fun _79_293 -> (match (_79_293) with
| (x, _79_292) -> begin
(let _178_168 = (FStar_All.pipe_left (fun _178_167 -> Some (_178_167)) (FStar_Absyn_Syntax.Implicit (true)))
in ((x), (_178_168)))
end)) tps)
in (FStar_Absyn_Util.close_typ _178_169 t))
in Some (t))
end else begin
None
end
end
| _79_296 -> begin
None
end)))
in (FStar_Util.must tr)))


let parseInductiveConstructors : context  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelts  ->  inductiveConstructor Prims.list = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _178_177 = (lookupDataConType c sigb h)
in {cname = h; ctype = _178_177})) cnames))


let rec parseInductiveTypesFromSigBundle : context  ->  FStar_Absyn_Syntax.sigelts  ->  (inductiveTypeFam Prims.list * typeAbbrev Prims.list * inductiveConstructor Prims.list) = (fun c sigs -> (match (sigs) with
| [] -> begin
(([]), ([]), ([]))
end
| (FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _79_310, constrs, qs, _79_314))::tlsig -> begin
(

let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (

let _79_322 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_79_322) with
| (inds, abbs, exns) -> begin
((({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds), (abbs), (exns))
end)))
end
| (FStar_Absyn_Syntax.Sig_datacon (l, _79_326, tc, quals, lids, _79_331))::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(

let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (

let _79_336 = ()
in (([]), ([]), (({cname = l; ctype = t})::[]))))
end else begin
(([]), ([]), ([]))
end
end
| (FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _79_342, t, _79_345, _79_347))::tlsig -> begin
(

let _79_354 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_79_354) with
| (inds, abbs, exns) -> begin
((inds), (({abTyName = l; abTyBinders = bs; abBody = t})::abbs), (exns))
end))
end
| (se)::tlsig -> begin
(let _178_183 = (let _178_182 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _178_182))
in (failwith _178_183))
end))


let lident2mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun l -> l.FStar_Ident.ident.FStar_Ident.idText)


let totalType_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _79_363 -> begin
(failwith "expected a total type. constructors of inductive types were assumed to be total")
end))


let allBindersOfFuntype : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.binder Prims.list = (fun c t -> (

let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _79_372 -> begin
[]
end)))


let bindersOfFuntype : context  ->  Prims.int  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Absyn_Syntax.typ) = (fun c n t -> (

let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(

let _79_383 = (FStar_Util.first_N n lb)
in (match (_79_383) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _178_198 = (totalType_of_comp cp)
in ((ll), (_178_198)))
end else begin
(let _178_199 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in ((ll), (_178_199)))
end
end))
end
| _79_385 -> begin
(

let _79_386 = ()
in (([]), (t)))
end)))


let rec zipUnequal = (fun la lb -> (match (((la), (lb))) with
| ((ha)::ta, (hb)::tb) -> begin
(let _178_204 = (zipUnequal ta tb)
in (((ha), (hb)))::_178_204)
end
| _79_400 -> begin
[]
end))


let mlTyIdentOfBinder : FStar_Absyn_Syntax.binder  ->  (Prims.string * Prims.int) = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))


let extractCtor : FStar_Absyn_Syntax.binder Prims.list  ->  context  ->  inductiveConstructor  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlty Prims.list)) = (fun tyBinders c ctor -> (

let _79_407 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_79_407) with
| (lb, tr) -> begin
(

let _79_408 = ()
in (

let lp = (FStar_List.zip tyBinders lb)
in (

let newC = (let _178_214 = (FStar_List.map (fun _79_413 -> (match (_79_413) with
| (x, y) -> begin
(((Prims.fst x)), ((Prims.fst y)))
end)) lp)
in (extendContextWithRepAsTyVars _178_214 c))
in (

let mlt = (let _178_215 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) _178_215))
in (

let tys = (let _178_216 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in ((_178_216), (mlt)))
in (

let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _178_219 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (let _178_218 = (let _178_217 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident2mlsymbol ctor.cname)), (_178_217)))
in ((_178_219), (_178_218))))))))))
end)))


let rec firstNNats : Prims.int  ->  Prims.int Prims.list = (fun n -> if ((Prims.parse_int "0") < n) then begin
(let _178_222 = (firstNNats (n - (Prims.parse_int "1")))
in (n)::_178_222)
end else begin
[]
end)


let dummyIdent : Prims.int  ->  (Prims.string * Prims.int) = (fun n -> (let _178_226 = (let _178_225 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _178_225))
in ((_178_226), ((Prims.parse_int "0")))))


let dummyIndexIdents : Prims.int  ->  (Prims.string * Prims.int) Prims.list = (fun n -> (let _178_229 = (firstNNats n)
in (FStar_List.map dummyIdent _178_229)))


let extractInductive : context  ->  inductiveTypeFam  ->  (context * (Prims.bool * FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlsymbol Prims.option * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c ind -> (

let newContext = c
in (

let nIndices = (numIndices ind.k ind.tyName.FStar_Ident.ident.FStar_Ident.idText)
in (

let _79_427 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_79_427) with
| (nc, tyb) -> begin
(

let mlbs = (let _178_235 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _178_234 = (dummyIndexIdents nIndices)
in (FStar_List.append _178_235 _178_234)))
in (

let tbody = (match ((FStar_Util.find_opt (fun _79_1 -> (match (_79_1) with
| FStar_Absyn_Syntax.RecordType (_79_431) -> begin
true
end
| _79_434 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(

let _79_438 = ()
in (

let _79_443 = (FStar_List.hd tyb)
in (match (_79_443) with
| (_79_441, c_ty) -> begin
(

let _79_444 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> ((lid.FStar_Ident.ident.FStar_Ident.idText), (ty))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _79_450 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in ((nc), (((false), ((lident2mlsymbol ind.tyName)), (None), (mlbs), (Some (tbody)))))))
end)))))


let mfst = (fun x -> (FStar_List.map Prims.fst x))


let rec headBinders : context  ->  FStar_Absyn_Syntax.typ  ->  (context * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.typ) = (fun c t -> (

let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(

let _79_463 = (let _178_245 = (let _178_244 = (mfst bs)
in (extendContext c _178_244))
in (headBinders _178_245 t))
in (match (_79_463) with
| (c, rb, rresidualType) -> begin
((c), ((FStar_List.append bs rb)), (rresidualType))
end))
end
| _79_465 -> begin
((c), ([]), (t))
end)))


let extractTypeAbbrev : FStar_Absyn_Syntax.qualifier Prims.list  ->  context  ->  typeAbbrev  ->  (context * (Prims.bool * FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlsymbol Prims.option * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun quals c tyab -> (

let bs = tyab.abTyBinders
in (

let t = tyab.abBody
in (

let l = tyab.abTyName
in (

let c = (let _178_252 = (mfst bs)
in (extendContext c _178_252))
in (

let _79_476 = (headBinders c t)
in (match (_79_476) with
| (c, headBinders, residualType) -> begin
(

let bs = (FStar_List.append bs headBinders)
in (

let t = residualType
in (

let mlt = (extractTyp c t)
in (

let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) mlt)
in (

let tyDecBody = FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (

let assumed = (FStar_Util.for_some (fun _79_2 -> (match (_79_2) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _79_485 -> begin
false
end)) quals)
in (

let td = (let _178_254 = (FStar_List.map mlTyIdentOfBinder bs)
in ((assumed), ((mlsymbolOfLident l)), (None), (_178_254), (Some (tyDecBody))))
in (

let c = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_3 -> (match (_79_3) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.New) -> begin
true
end
| _79_492 -> begin
false
end)))) then begin
c
end else begin
(FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
end
in ((c), (td))))))))))
end)))))))


let extractExn : context  ->  inductiveConstructor  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1) = (fun c exnConstr -> (

let mlt = (extractTyp c exnConstr.ctype)
in (

let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) mlt)
in (

let tys = (([]), (mlt))
in (

let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (

let ex_decl = (let _178_261 = (let _178_260 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident2mlsymbol exnConstr.cname)), (_178_260)))
in FStar_Extraction_ML_Syntax.MLM_Exn (_178_261))
in (let _178_262 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in ((_178_262), (ex_decl)))))))))


let rec extractSigElt : context  ->  FStar_Absyn_Syntax.sigelt  ->  (context * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _79_506, t, quals, range) -> begin
(

let _79_514 = (extractTypeAbbrev quals c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_79_514) with
| (c, tds) -> begin
(let _178_269 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(let _178_268 = (let _178_267 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_178_267))
in (_178_268)::(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end
in ((c), (_178_269)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, (FStar_Absyn_Syntax.ExceptionConstructor)::[], _79_519, range) -> begin
(

let _79_528 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_79_528) with
| (_79_524, _79_526, exConstrs) -> begin
(

let _79_529 = ()
in (

let _79_533 = (let _178_270 = (FStar_List.hd exConstrs)
in (extractExn c _178_270))
in (match (_79_533) with
| (c, exDecl) -> begin
(let _178_273 = (let _178_272 = (let _178_271 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_178_271))
in (_178_272)::(exDecl)::[])
in ((c), (_178_273)))
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _79_536, _79_538, range) -> begin
(

let _79_546 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_79_546) with
| (inds, abbs, _79_545) -> begin
(

let _79_549 = (FStar_Util.fold_map extractInductive c inds)
in (match (_79_549) with
| (c, indDecls) -> begin
(

let _79_552 = (FStar_Util.fold_map (extractTypeAbbrev []) c abbs)
in (match (_79_552) with
| (c, tyAbDecls) -> begin
(let _178_276 = (let _178_275 = (let _178_274 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_178_274))
in (_178_275)::(FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
in ((c), (_178_276)))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, k, _79_557, _79_559, quals, r) -> begin
if (((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_4 -> (match (_79_4) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _79_572 -> begin
false
end))))))) then begin
(

let _79_576 = (FStar_Absyn_Util.kind_formals k)
in (match (_79_576) with
| (kbs, _79_575) -> begin
(

let se = FStar_Absyn_Syntax.Sig_typ_abbrev (((l), ((FStar_List.append bs kbs)), (FStar_Absyn_Syntax.mk_Kind_type), (FStar_Tc_Recheck.t_unit), (quals), (r)))
in (extractSigElt c se))
end))
end else begin
((c), ([]))
end
end
| _79_579 -> begin
((c), ([]))
end))




