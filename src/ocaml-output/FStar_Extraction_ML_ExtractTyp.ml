
open Prims
let binderIsExp = (fun bn -> (FStar_Absyn_Print.is_inr (Prims.fst bn)))

let rec argIsExp = (fun k typeName -> (match ((let _126_7 = (FStar_Absyn_Util.compress_kind k)
in _126_7.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _126_9 = (FStar_List.map binderIsExp bs)
in (let _126_8 = (argIsExp r typeName)
in (FStar_List.append _126_9 _126_8)))
end
| FStar_Absyn_Syntax.Kind_delayed (k, _61_13, _61_15) -> begin
(FStar_All.failwith "extraction.numIndices : expected a compressed argument")
end
| FStar_Absyn_Syntax.Kind_abbrev (_61_19, k) -> begin
(argIsExp k typeName)
end
| _61_24 -> begin
(FStar_All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))

let numIndices = (fun k typeName -> (let _126_14 = (argIsExp k typeName)
in (FStar_List.length _126_14)))

let mlty_of_isExp = (fun b -> if b then begin
FStar_Extraction_ML_Env.erasedContent
end else begin
FStar_Extraction_ML_Env.unknownType
end)

let delta_norm_eff = (let cache = (FStar_Util.smap_create 20)
in (let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(let res = (match ((FStar_Tc_Env.lookup_effect_abbrev g.FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some (_61_37, c) -> begin
(delta_norm_eff g (FStar_Absyn_Util.comp_effect_name c))
end)
in (let _61_42 = (FStar_Util.smap_add cache l.FStar_Absyn_Syntax.str res)
in res))
end))
in delta_norm_eff))

let translate_eff = (fun g l -> (let l = (delta_norm_eff g l)
in if (FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))

let rec curry = (fun inp f out -> (match (inp) with
| [] -> begin
out
end
| h::[] -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _126_34 = (let _126_33 = (curry ((h2)::tl) f out)
in (h1, FStar_Extraction_ML_Syntax.E_PURE, _126_33))
in FStar_Extraction_ML_Syntax.MLTY_Fun (_126_34))
end))

type context =
FStar_Extraction_ML_Env.env

let extendContextWithRepAsTyVar = (fun b c -> (match (b) with
| (FStar_Util.Inl (bt), FStar_Util.Inl (btr)) -> begin
(FStar_Extraction_ML_Env.extend_ty c btr (Some (FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (FStar_Util.Inr (bv), FStar_Util.Inr (_61_68)) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false)
end
| _61_72 -> begin
(FStar_All.failwith "Impossible case")
end))

let extendContextWithRepAsTyVars = (fun b c -> (FStar_List.fold_right extendContextWithRepAsTyVar b c))

let extendContextAsTyvar = (fun availableInML b c -> (match (b) with
| FStar_Util.Inl (bt) -> begin
(FStar_Extraction_ML_Env.extend_ty c bt (Some (if availableInML then begin
FStar_Extraction_ML_Syntax.MLTY_Var ((FStar_Extraction_ML_Env.btvar_as_mltyvar bt))
end else begin
FStar_Extraction_ML_Env.unknownType
end)))
end
| FStar_Util.Inr (bv) -> begin
(FStar_Extraction_ML_Env.extend_bv c bv ([], FStar_Extraction_ML_Env.erasedContent) false false)
end))

let extendContext = (fun c tyVars -> (FStar_List.fold_right (extendContextAsTyvar true) tyVars c))

let isTypeScheme = (fun i c -> true)

let preProcType = (fun c ft -> (let ft = (FStar_Absyn_Util.compress_typ ft)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) c.FStar_Extraction_ML_Env.tcenv ft)))

let extractTyVar = (fun c btv -> (FStar_Extraction_ML_Env.lookup_tyvar c btv))

let rec extractTyp = (fun c ft -> (let ft = (preProcType c ft)
in (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| FStar_Absyn_Syntax.Typ_fun (bs, codomain) -> begin
(let _61_104 = (extractBindersTypes c bs)
in (match (_61_104) with
| (bts, newC) -> begin
(let _61_107 = (extractComp newC codomain)
in (match (_61_107) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (bv, _61_110) -> begin
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
(let _126_86 = (FStar_Extraction_ML_Util.mkTypApp tyin (FStar_List.append argsin arrgs) ty)
in (extractTyp c _126_86))
end
| _61_127 -> begin
FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(let _61_135 = (extractBindersTypes c bs)
in (match (_61_135) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (ty, _61_138) -> begin
(extractTyp c ty)
end
| FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| FStar_Absyn_Syntax.Typ_uvar (_61_144) -> begin
FStar_Extraction_ML_Env.unknownType
end
| FStar_Absyn_Syntax.Typ_delayed (_61_147) -> begin
(FStar_All.failwith "expected the argument to be compressed")
end
| _61_150 -> begin
(FStar_All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg = (fun c a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| FStar_Util.Inr (_61_156) -> begin
FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta = (fun c mt -> (match (mt) with
| (FStar_Absyn_Syntax.Meta_pattern (t, _)) | (FStar_Absyn_Syntax.Meta_named (t, _)) | (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _)) | (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _)) | (FStar_Absyn_Syntax.Meta_slack_formula (t, _, _)) -> begin
(extractTyp c t)
end))
and extractTyConstApp = (fun c ftv ags -> if (isTypeScheme ftv.FStar_Absyn_Syntax.v c) then begin
(let mlargs = (FStar_List.map (getTypeFromArg c) ags)
in (let k = ftv.FStar_Absyn_Syntax.sort
in (let ar = (argIsExp k ftv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
in (let _61_198 = (FStar_Util.first_N (FStar_List.length mlargs) ar)
in (match (_61_198) with
| (_61_196, missingArgs) -> begin
(let argCompletion = (FStar_List.map mlty_of_isExp missingArgs)
in (let _126_98 = (let _126_97 = (FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.FStar_Absyn_Syntax.v)
in ((FStar_List.append mlargs argCompletion), _126_97))
in FStar_Extraction_ML_Syntax.MLTY_Named (_126_98)))
end)))))
end else begin
(FStar_All.failwith "this case was not anticipated")
end)
and extractBinderType = (fun c bn -> (match (bn) with
| (FStar_Util.Inl (btv), _61_205) -> begin
(let _126_102 = (extractKind c btv.FStar_Absyn_Syntax.sort)
in (let _126_101 = (extendContextAsTyvar false (FStar_Util.Inl (btv)) c)
in (_126_102, _126_101)))
end
| (FStar_Util.Inr (bvv), _61_210) -> begin
(let _126_104 = (extractTyp c bvv.FStar_Absyn_Syntax.sort)
in (let _126_103 = (extendContextAsTyvar false (FStar_Util.Inr (bvv)) c)
in (_126_104, _126_103)))
end))
and extractBindersTypes = (fun c bs -> (let _126_110 = (FStar_List.fold_left (fun _61_216 b -> (match (_61_216) with
| (lt, cp) -> begin
(let _61_220 = (extractBinderType cp b)
in (match (_61_220) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _61_223 -> (match (_61_223) with
| (x, c) -> begin
((FStar_List.rev x), c)
end)) _126_110)))
and extractKind = (fun c ft -> FStar_Extraction_ML_Env.erasedContent)
and extractComp = (fun c ft -> (extractComp' c ft.FStar_Absyn_Syntax.n))
and extractComp' = (fun c ft -> (match (ft) with
| FStar_Absyn_Syntax.Total (ty) -> begin
(let _126_117 = (extractTyp c ty)
in (_126_117, FStar_Extraction_ML_Syntax.E_PURE))
end
| FStar_Absyn_Syntax.Comp (cm) -> begin
(let _126_119 = (extractTyp c cm.FStar_Absyn_Syntax.result_typ)
in (let _126_118 = (translate_eff c cm.FStar_Absyn_Syntax.effect_name)
in (_126_119, _126_118)))
end))

let binderPPnames = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _61_238) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
| (FStar_Util.Inr (bvv), _61_243) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end))

let binderRealnames = (fun bn -> (match (bn) with
| (FStar_Util.Inl (btv), _61_249) -> begin
btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end
| (FStar_Util.Inr (bvv), _61_254) -> begin
bvv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname
end))

let mlsymbolOfLident = (fun id -> id.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)

type inductiveConstructor =
{cname : FStar_Absyn_Syntax.lident; ctype : FStar_Absyn_Syntax.typ}

let is_MkinductiveConstructor = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveConstructor")))

type inductiveTypeFam =
{tyName : FStar_Absyn_Syntax.lident; k : FStar_Absyn_Syntax.knd; tyBinders : FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : FStar_Absyn_Syntax.qualifier Prims.list}

let is_MkinductiveTypeFam = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_MkinductiveTypeFam")))

type typeAbbrev =
{abTyName : FStar_Absyn_Syntax.lident; abTyBinders : FStar_Absyn_Syntax.binders; abBody : FStar_Absyn_Syntax.typ}

let is_MktypeAbbrev = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_MktypeAbbrev")))

let lookupDataConType = (fun c sigb l -> (let tr = (FStar_Util.find_map sigb (fun s -> (match (s) with
| FStar_Absyn_Syntax.Sig_datacon (l', t, (_61_277, tps, _61_280), quals, lids, _61_285) -> begin
if (l = l') then begin
(let t = (let _126_167 = (FStar_List.map (fun _61_291 -> (match (_61_291) with
| (x, _61_290) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _126_167 t))
in Some (t))
end else begin
None
end
end
| _61_294 -> begin
None
end)))
in (FStar_Util.must tr)))

let parseInductiveConstructors = (fun c cnames sigb -> (FStar_List.map (fun h -> (let _126_175 = (lookupDataConType c sigb h)
in {cname = h; ctype = _126_175})) cnames))

let rec parseInductiveTypesFromSigBundle = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _61_308, constrs, qs, _61_312)::tlsig -> begin
(let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (let _61_320 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_61_320) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, _61_324, tc, quals, lids, _61_329)::tlsig -> begin
if (FStar_List.contains FStar_Absyn_Syntax.ExceptionConstructor quals) then begin
(let t = (FStar_Tc_Env.lookup_datacon c.FStar_Extraction_ML_Env.tcenv l)
in (let _61_334 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end else begin
([], [], [])
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _61_340, t, _61_343, _61_345)::tlsig -> begin
(let _61_352 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_61_352) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _126_181 = (let _126_180 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _126_180))
in (FStar_All.failwith _126_181))
end))

let rec argTypes = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, _61_359, b) -> begin
(let _126_184 = (argTypes b)
in (a)::_126_184)
end
| _61_364 -> begin
[]
end))

let lident2mlsymbol = (fun l -> l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)

let totalType_of_comp = (fun ft -> (match (ft.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _61_370 -> begin
(FStar_All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

let allBindersOfFuntype = (fun c t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _61_379 -> begin
[]
end)))

let bindersOfFuntype = (fun c n t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(let _61_390 = (FStar_Util.first_N n lb)
in (match (_61_390) with
| (ll, lr) -> begin
if (FStar_List.isEmpty lr) then begin
(let _126_199 = (totalType_of_comp cp)
in (ll, _126_199))
end else begin
(let _126_200 = (FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _126_200))
end
end))
end
| _61_392 -> begin
(let _61_393 = ()
in ([], t))
end)))

let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _126_205 = (zipUnequal ta tb)
in ((ha, hb))::_126_205)
end
| _61_407 -> begin
[]
end))

let mlTyIdentOfBinder = (fun b -> (FStar_Extraction_ML_Env.prependTick (FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

let extractCtor = (fun tyBinders c ctor -> (let _61_414 = (bindersOfFuntype c (FStar_List.length tyBinders) ctor.ctype)
in (match (_61_414) with
| (lb, tr) -> begin
(let _61_415 = ()
in (let lp = (FStar_List.zip tyBinders lb)
in (let newC = (let _126_215 = (FStar_List.map (fun _61_420 -> (match (_61_420) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _126_215 c))
in (let mlt = (let _126_216 = (extractTyp newC tr)
in (FStar_Extraction_ML_Util.eraseTypeDeep c _126_216))
in (let tys = (let _126_217 = (FStar_List.map mlTyIdentOfBinder tyBinders)
in (_126_217, mlt))
in (let fvv = (FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _126_220 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false)
in (let _126_219 = (let _126_218 = (argTypes mlt)
in ((lident2mlsymbol ctor.cname), _126_218))
in (_126_220, _126_219)))))))))
end)))

let rec firstNNats = (fun n -> if (0 < n) then begin
(let _126_223 = (firstNNats (n - 1))
in (n)::_126_223)
end else begin
[]
end)

let dummyIdent = (fun n -> (let _126_227 = (let _126_226 = (FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _126_226))
in (_126_227, 0)))

let dummyIndexIdents = (fun n -> (let _126_230 = (firstNNats n)
in (FStar_List.map dummyIdent _126_230)))

let extractInductive = (fun c ind -> (let newContext = c
in (let nIndices = (numIndices ind.k ind.tyName.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)
in (let _61_434 = (FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_61_434) with
| (nc, tyb) -> begin
(let mlbs = (let _126_236 = (FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _126_235 = (dummyIndexIdents nIndices)
in (FStar_List.append _126_236 _126_235)))
in (let tbody = (match ((FStar_Util.find_opt (fun _61_1 -> (match (_61_1) with
| FStar_Absyn_Syntax.RecordType (_61_438) -> begin
true
end
| _61_441 -> begin
false
end)) ind.qualifiers)) with
| Some (FStar_Absyn_Syntax.RecordType (ids)) -> begin
(let _61_445 = ()
in (let _61_450 = (FStar_List.hd tyb)
in (match (_61_450) with
| (_61_448, c_ty) -> begin
(let _61_451 = ()
in (let fields = (FStar_List.map2 (fun lid ty -> (lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText, ty)) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _61_457 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

let mfst = (fun x -> (FStar_List.map Prims.fst x))

let rec headBinders = (fun c t -> (let t = (preProcType c t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _61_470 = (let _126_246 = (let _126_245 = (mfst bs)
in (extendContext c _126_245))
in (headBinders _126_246 t))
in (match (_61_470) with
| (c, rb, rresidualType) -> begin
(c, (FStar_List.append bs rb), rresidualType)
end))
end
| _61_472 -> begin
(c, [], t)
end)))

let extractTypeAbbrev = (fun c tyab -> (let bs = tyab.abTyBinders
in (let t = tyab.abBody
in (let l = tyab.abTyName
in (let c = (let _126_251 = (mfst bs)
in (extendContext c _126_251))
in (let _61_482 = (headBinders c t)
in (match (_61_482) with
| (c, headBinders, residualType) -> begin
(let bs = (FStar_List.append bs headBinders)
in (let t = residualType
in (let mlt = (extractTyp c t)
in (let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tyDecBody = FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (let td = (let _126_252 = (FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _126_252, Some (tyDecBody)))
in (let c = (FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
in (c, td))))))))
end)))))))

let extractExn = (fun c exnConstr -> (let mlt = (extractTyp c exnConstr.ctype)
in (let mlt = (FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tys = ([], mlt)
in (let fvv = (FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (let ex_decl = (let _126_258 = (let _126_257 = (argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _126_257))
in FStar_Extraction_ML_Syntax.MLM_Exn (_126_258))
in (let _126_259 = (FStar_Extraction_ML_Env.extend_fv c fvv tys false)
in (_126_259, ex_decl))))))))

let rec extractSigElt = (fun c s -> (match (s) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _61_502, t, quals, _61_506) -> begin
(let _61_511 = (extractTypeAbbrev c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_61_511) with
| (c, tds) -> begin
(let _126_264 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Logic)) then begin
[]
end else begin
(FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[]
end
in (c, _126_264))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, FStar_Absyn_Syntax.ExceptionConstructor::[], _61_516, _61_518) -> begin
(let _61_526 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_61_526) with
| (_61_522, _61_524, exConstrs) -> begin
(let _61_527 = ()
in (let _61_531 = (let _126_265 = (FStar_List.hd exConstrs)
in (extractExn c _126_265))
in (match (_61_531) with
| (c, exDecl) -> begin
(c, (exDecl)::[])
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (sigs, _61_534, _61_536, _61_538) -> begin
(let _61_545 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_61_545) with
| (inds, abbs, _61_544) -> begin
(let _61_548 = (FStar_Util.fold_map extractInductive c inds)
in (match (_61_548) with
| (c, indDecls) -> begin
(let _61_551 = (FStar_Util.fold_map extractTypeAbbrev c abbs)
in (match (_61_551) with
| (c, tyAbDecls) -> begin
(c, (FStar_Extraction_ML_Syntax.MLM_Ty ((FStar_List.append indDecls tyAbDecls)))::[])
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (_61_553, _61_555, _61_557, _61_559, _61_561, quals, _61_564) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) && (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_2 -> (match (_61_2) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _61_575 -> begin
false
end))))))) then begin
(extractSigElt c (FStar_Absyn_Syntax.Sig_bundle (((s)::[], (FStar_Absyn_Syntax.Assumption)::[], [], (FStar_Absyn_Util.range_of_sigelt s)))))
end else begin
(c, [])
end
end
| _61_577 -> begin
(c, [])
end))




