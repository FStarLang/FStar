
open Prims

let binderIsExp : FStar_Absyn_Syntax.binder  ->  Prims.bool = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))


let rec argIsExp : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.bool Prims.list = (fun k typeName -> (match ((let _163_7 = (FStar_Absyn_Util.compress_kind k)
in _163_7.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _163_9 = (FStar_List.map binderIsExp bs)
in (let _163_8 = (argIsExp r typeName)
in (FStar_List.append _163_9 _163_8)))
end
| FStar_Absyn_Syntax.Kind_delayed (k, _74_14, _74_16) -> begin
(FStar_All.failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_74_20, k) -> begin
(argIsExp k typeName)
end
| _74_25 -> begin
(FStar_All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))


let numIndices : FStar_Absyn_Syntax.knd  ->  Prims.string  ->  Prims.nat = (fun k typeName -> (let _163_14 = (argIsExp k typeName)
in (FStar_List.length _163_14)))


let mlty_of_isExp : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlty = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)


let delta_norm_eff : FStar_Extraction_ML_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create 20)
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
| Some (_74_38, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (

let _74_43 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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
| h::[] -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _163_34 = (let _163_33 = (curry ((h2)::tl) f out)
in (h1, FStar_Extraction_ML_Syntax.E_PURE, _163_33))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_163_34))
end))


type context =
FStar_Extraction_ML_Env.env


let extendContextWithRepAsTyVar : ((FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either * (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either)  ->  context  ->  context = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_74_69)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false false)
end
| _74_73 -> begin
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

let _74_105 = (extractBindersTypes c bs)
in (match (_74_105) with
| (bts, newC) -> begin
(

let _74_108 = (extractComp newC codomain)
in (match (_74_108) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _74_111) -> begin
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
(let _163_86 = (FStar_Extraction_ML_Util.mkTypApp tyin (FStar_List.append argsin arrgs) ty)
in (extractTyp c _163_86))
end
| _74_128 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(

let _74_136 = (extractBindersTypes c bs)
in (match (_74_136) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _74_139) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_74_145) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_74_148) -> begin
(FStar_All.failwith "expected the argument to be compressed")
end
| _74_151 -> begin
(FStar_All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg : context  ->  FStar_Absyn_Syntax.arg  ->  FStar_Extraction_ML_Syntax.mlty = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_74_157) -> begin
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

let _74_199 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_74_199) with
| (_74_197, missingArgs) -> begin
(

let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _163_98 = (let _163_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in ((FStar_List.append mlargs argCompletion), _163_97))
in FStar_Extraction_ML_Syntax.MLTY_Named (_163_98)))
end)))))
end else begin
(FStar_All.failwith "this case was not anticipated")
end)
and extractBinderType : context  ->  FStar_Absyn_Syntax.binder  ->  (FStar_Extraction_ML_Syntax.mlty * context) = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _74_206) -> begin
(let _163_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _163_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in (_163_102, _163_101)))
end
| (FStar_Util.Inr (bvv), _74_211) -> begin
(let _163_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _163_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in (_163_104, _163_103)))
end))
and extractBindersTypes : context  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * context) = (fun c bs -> (let _163_110 = (FStar_List.fold_left (fun _74_217 b -> (match (_74_217) with
| (lt, cp) -> begin
(

let _74_221 = (extractBinderType cp b)
in (match (_74_221) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _74_224 -> (match (_74_224) with
| (x, c) -> begin
((FStar_List.rev x), c)
end)) _163_110)))
and extractKind : context  ->  FStar_Absyn_Syntax.knd  ->  FStar_Extraction_ML_Syntax.mlty = (fun c ft -> FStar_Extraction_ML_Env.erasedContent)
and extractComp : context  ->  FStar_Absyn_Syntax.comp  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (extractComp' c ft.FStar_Absyn_Syntax.n))
and extractComp' : context  ->  FStar_Absyn_Syntax.comp'  ->  (FStar_Extraction_ML_Syntax.mlty * FStar_Extraction_ML_Syntax.e_tag) = (fun c ft -> (match (ft) with
| FStar_Absyn_Syntax.Total (ty) -> begin
(let _163_117 = (extractTyp c ty)
in (_163_117, FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Absyn_Syntax.Comp (cm) -> begin
(let _163_119 = (extractTyp c cm.FStar_Absyn_Syntax.result_typ)
in (let _163_118 = (translate_eff c cm.FStar_Absyn_Syntax.effect_name)
in (_163_119, _163_118)))
end))


let binderPPnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _74_239) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _74_244) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))


let binderRealnames : FStar_Absyn_Syntax.binder  ->  FStar_Ident.ident = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _74_250) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _74_255) -> begin
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


let lookupDataConType : context  ->  FStar_Absyn_Syntax.sigelts  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun c sigb l -> (

let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_74_278, tps, _74_281), quals, lids, _74_286) -> begin
if (l = l') then begin
(

let t = (let _163_169 = (FStar_List.map (fun _74_292 -> (match (_74_292) with
| (x, _74_291) -> begin
(let _163_168 = (FStar_All.pipe_left (fun _163_167 -> Some (_163_167)) (FStar_Absyn_Syntax.Implicit (true)))
in (x, _163_168))
end)) tps)
in (FStar_Absyn_Util.close_typ _163_169 t))
in Some (t))
end else begin
None
end
end
| _74_295 -> begin
None
end)))
in (FStar_Util.must tr)))


let parseInductiveConstructors : context  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelts  ->  inductiveConstructor Prims.list = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _163_177 = (lookupDataConType c sigb h)
in {cname = h; ctype = _163_177})) cnames))


let rec parseInductiveTypesFromSigBundle : context  ->  FStar_Absyn_Syntax.sigelts  ->  (inductiveTypeFam Prims.list * typeAbbrev Prims.list * inductiveConstructor Prims.list) = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _74_309, constrs, qs, _74_313)::tlsig -> begin
(

let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (

let _74_321 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_74_321) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, _74_325, tc, quals, lids, _74_330)::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(

let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (

let _74_335 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end else begin
([], [], [])
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _74_341, t, _74_344, _74_346)::tlsig -> begin
(

let _74_353 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_74_353) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _163_183 = (let _163_182 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _163_182))
in (FStar_All.failwith _163_183))
end))


let lident2mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun l -> l.FStar_Ident.ident.FStar_Ident.idText)


let totalType_of_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.typ = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _74_362 -> begin
(FStar_All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))


let allBindersOfFuntype : context  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.binder Prims.list = (fun c t -> (

let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _74_371 -> begin
[]
end)))


let bindersOfFuntype : context  ->  Prims.int  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Absyn_Syntax.typ) = (fun c n t -> (

let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(

let _74_382 = (FStar_Util.first_N n lb)
in (match (_74_382) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _163_198 = (totalType_of_comp cp)
in (ll, _163_198))
end else begin
(let _163_199 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _163_199))
end
end))
end
| _74_384 -> begin
(

let _74_385 = ()
in ([], t))
end)))


let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _163_204 = (zipUnequal ta tb)
in ((ha, hb))::_163_204)
end
| _74_399 -> begin
[]
end))


let mlTyIdentOfBinder : FStar_Absyn_Syntax.binder  ->  (Prims.string * Prims.int) = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))


let extractCtor : FStar_Absyn_Syntax.binder Prims.list  ->  context  ->  inductiveConstructor  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlty Prims.list)) = (fun tyBinders c ctor -> (

let _74_406 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_74_406) with
| (lb, tr) -> begin
(

let _74_407 = ()
in (

let lp = (FStar_List.zip tyBinders lb)
in (

let newC = (let _163_214 = (FStar_List.map (fun _74_412 -> (match (_74_412) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _163_214 c))
in (

let mlt = (let _163_215 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) _163_215))
in (

let tys = (let _163_216 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in (_163_216, mlt))
in (

let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _163_219 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (let _163_218 = (let _163_217 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident2mlsymbol ctor.cname), _163_217))
in (_163_219, _163_218)))))))))
end)))


let rec firstNNats : Prims.int  ->  Prims.int Prims.list = (fun n -> if (0 < n) then begin
(let _163_222 = (firstNNats (n - 1))
in (n)::_163_222)
end else begin
[]
end)


let dummyIdent : Prims.int  ->  (Prims.string * Prims.int) = (fun n -> (let _163_226 = (let _163_225 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _163_225))
in (_163_226, 0)))


let dummyIndexIdents : Prims.int  ->  (Prims.string * Prims.int) Prims.list = (fun n -> (let _163_229 = (firstNNats n)
in (FStar_List.map dummyIdent _163_229)))


let extractInductive : context  ->  inductiveTypeFam  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun c ind -> (

let newContext = c
in (

let nIndices = (numIndices ind.k ind.tyName.FStar_Ident.ident.FStar_Ident.idText)
in (

let _74_426 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_74_426) with
| (nc, tyb) -> begin
(

let mlbs = (let _163_235 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _163_234 = (dummyIndexIdents nIndices)
in (FStar_List.append _163_235 _163_234)))
in (

let tbody = (match ((FStar_Util.find_opt (fun _74_1 -> (match (_74_1) with
| FStar_Absyn_Syntax.RecordType (_74_430) -> begin
true
end
| _74_433 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(

let _74_437 = ()
in (

let _74_442 = (FStar_List.hd tyb)
in (match (_74_442) with
| (_74_440, c_ty) -> begin
(

let _74_443 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> (lid.FStar_Ident.ident.FStar_Ident.idText, ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _74_449 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))


let mfst = (fun x -> (FStar_List.map Prims.fst x))


let rec headBinders : context  ->  FStar_Absyn_Syntax.typ  ->  (context * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.typ) = (fun c t -> (

let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(

let _74_462 = (let _163_245 = (let _163_244 = (mfst bs)
in (extendContext c _163_244))
in (headBinders _163_245 t))
in (match (_74_462) with
| (c, rb, rresidualType) -> begin
(c, (FStar_List.append bs rb), rresidualType)
end))
end
| _74_464 -> begin
(c, [], t)
end)))


let extractTypeAbbrev : FStar_Absyn_Syntax.qualifier Prims.list  ->  context  ->  typeAbbrev  ->  (context * (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mltybody Prims.option)) = (fun quals c tyab -> (

let bs = tyab.abTyBinders
in (

let t = tyab.abBody
in (

let l = tyab.abTyName
in (

let c = (let _163_252 = (mfst bs)
in (extendContext c _163_252))
in (

let _74_475 = (headBinders c t)
in (match (_74_475) with
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

let td = (let _163_253 = (FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _163_253, Some (tyDecBody)))
in (

let c = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _74_2 -> (match (_74_2) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.New) -> begin
true
end
| _74_486 -> begin
false
end)))) then begin
c
end else begin
(FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
end
in (c, td))))))))
end)))))))


let extractExn : context  ->  inductiveConstructor  ->  (FStar_Extraction_ML_Env.env * FStar_Extraction_ML_Syntax.mlmodule1) = (fun c exnConstr -> (

let mlt = (extractTyp c exnConstr.ctype)
in (

let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.delta_unfold c) mlt)
in (

let tys = ([], mlt)
in (

let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (

let ex_decl = (let _163_260 = (let _163_259 = (FStar_Extraction_ML_Util.argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _163_259))
in FStar_Extraction_ML_Syntax.MLM_Exn (_163_260))
in (let _163_261 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false false)
in (_163_261, ex_decl))))))))


let rec extractSigElt : context  ->  FStar_Absyn_Syntax.sigelt  ->  (context * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _74_500, t, quals, range) -> begin
(

let _74_508 = (extractTypeAbbrev quals c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_74_508) with
| (c, tds) -> begin
(let _163_268 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(let _163_267 = (let _163_266 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_163_266))
in (_163_267)::(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end
in (c, _163_268))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, FStar_Absyn_Syntax.ExceptionConstructor::[], _74_513, range) -> begin
(

let _74_522 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_74_522) with
| (_74_518, _74_520, exConstrs) -> begin
(

let _74_523 = ()
in (

let _74_527 = (let _163_269 = (FStar_List.hd exConstrs)
in (extractExn c _163_269))
in (match (_74_527) with
| (c, exDecl) -> begin
(let _163_272 = (let _163_271 = (let _163_270 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_163_270))
in (_163_271)::(exDecl)::[])
in (c, _163_272))
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _74_530, _74_532, range) -> begin
(

let _74_540 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_74_540) with
| (inds, abbs, _74_539) -> begin
(

let _74_543 = (FStar_Util.fold_map extractInductive c inds)
in (match (_74_543) with
| (c, indDecls) -> begin
(

let _74_546 = (FStar_Util.fold_map (extractTypeAbbrev []) c abbs)
in (match (_74_546) with
| (c, tyAbDecls) -> begin
(let _163_275 = (let _163_274 = (let _163_273 = (FStar_Extraction_ML_Util.mlloc_of_range range)
in FStar_Extraction_ML_Syntax.MLM_Loc (_163_273))
in (_163_274)::(FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
in (c, _163_275))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, k, _74_551, _74_553, quals, r) -> begin
if (((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _74_3 -> (match (_74_3) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _74_566 -> begin
false
end))))))) then begin
(

let _74_570 = (FStar_Absyn_Util.kind_formals k)
in (match (_74_570) with
| (kbs, _74_569) -> begin
(

let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((l, (FStar_List.append bs kbs), FStar_Absyn_Syntax.mk_Kind_type, FStar_Tc_Recheck.t_unit, quals, r))
in (extractSigElt c se))
end))
end else begin
(c, [])
end
end
| _74_573 -> begin
(c, [])
end))




