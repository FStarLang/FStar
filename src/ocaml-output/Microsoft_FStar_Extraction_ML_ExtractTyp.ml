
let binderIsExp = (fun bn -> (Microsoft_FStar_Absyn_Print.is_inr (Prims.fst bn)))

let rec argIsExp = (fun k typeName -> (match ((let _128_7 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _128_7.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (bs, r) -> begin
(let _128_9 = (Microsoft_FStar_List.map binderIsExp bs)
in (let _128_8 = (argIsExp r typeName)
in (Microsoft_FStar_List.append _128_9 _128_8)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (k, _62_13, _62_15) -> begin
(All.failwith "extraction.numIndices : expected a compressed argument")
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_62_19, k) -> begin
(argIsExp k typeName)
end
| _62_24 -> begin
(All.failwith (Prims.strcat "unexpected signature of inductive type" typeName))
end))

let numIndices = (fun k typeName -> (let _128_14 = (argIsExp k typeName)
in (Microsoft_FStar_List.length _128_14)))

let mlty_of_isExp = (fun b -> (match (b) with
| true -> begin
Microsoft_FStar_Extraction_ML_Env.erasedContent
end
| false -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end))

let delta_norm_eff = (let cache = (Microsoft_FStar_Util.smap_create 20)
in (let rec delta_norm_eff = (fun g l -> (match ((Microsoft_FStar_Util.smap_try_find cache l.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(let res = (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev g.Microsoft_FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some (_62_37, c) -> begin
(delta_norm_eff g (Microsoft_FStar_Absyn_Util.comp_effect_name c))
end)
in (let _62_42 = (Microsoft_FStar_Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str res)
in res))
end))
in delta_norm_eff))

let translate_eff = (fun g l -> (let l = (delta_norm_eff g l)
in (match (((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_PURE
end
| false -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE
end)))

let rec curry = (fun inp f out -> (match (inp) with
| [] -> begin
out
end
| h::[] -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _128_34 = (let _128_33 = (curry ((h2)::tl) f out)
in (h1, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _128_33))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_128_34))
end))

type context =
Microsoft_FStar_Extraction_ML_Env.env

let extendContextWithRepAsTyVar = (fun b c -> (match (b) with
| (Microsoft_FStar_Util.Inl (bt), Microsoft_FStar_Util.Inl (btr)) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_ty c btr (Some (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var ((Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (Microsoft_FStar_Util.Inr (bv), Microsoft_FStar_Util.Inr (_62_68)) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_bv c bv ([], Microsoft_FStar_Extraction_ML_Env.erasedContent) false false)
end
| _62_72 -> begin
(All.failwith "Impossible case")
end))

let extendContextWithRepAsTyVars = (fun b c -> (Microsoft_FStar_List.fold_right extendContextWithRepAsTyVar b c))

let extendContextAsTyvar = (fun availableInML b c -> (match (b) with
| Microsoft_FStar_Util.Inl (bt) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_ty c bt (Some ((match (availableInML) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var ((Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar bt))
end
| false -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end))))
end
| Microsoft_FStar_Util.Inr (bv) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_bv c bv ([], Microsoft_FStar_Extraction_ML_Env.erasedContent) false false)
end))

let extendContext = (fun c tyVars -> (Microsoft_FStar_List.fold_right (extendContextAsTyvar true) tyVars c))

let isTypeScheme = (fun i c -> true)

let preProcType = (fun c ft -> (let ft = (Microsoft_FStar_Absyn_Util.compress_typ ft)
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) c.Microsoft_FStar_Extraction_ML_Env.tcenv ft)))

let extractTyVar = (fun c btv -> (Microsoft_FStar_Extraction_ML_Env.lookup_tyvar c btv))

let rec extractTyp = (fun c ft -> (let ft = (preProcType c ft)
in (match (ft.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (bs, codomain) -> begin
(let _62_104 = (extractBindersTypes c bs)
in (match (_62_104) with
| (bts, newC) -> begin
(let _62_107 = (extractComp newC codomain)
in (match (_62_107) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (bv, _62_110) -> begin
(extractTyp c bv.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (ty, arrgs) -> begin
(let ty = (preProcType c ty)
in (let res = (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (tyin, argsin) -> begin
(let _128_86 = (Microsoft_FStar_Extraction_ML_Util.mkTypApp tyin (Microsoft_FStar_List.append argsin arrgs) ty)
in (extractTyp c _128_86))
end
| _62_127 -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (bs, ty) -> begin
(let _62_135 = (extractBindersTypes c bs)
in (match (_62_135) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (ty, _62_138) -> begin
(extractTyp c ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_62_144) -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_62_147) -> begin
(All.failwith "expected the argument to be compressed")
end
| _62_150 -> begin
(All.failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg = (fun c a -> (match ((Prims.fst a)) with
| Microsoft_FStar_Util.Inl (ty) -> begin
(extractTyp c ty)
end
| Microsoft_FStar_Util.Inr (_62_156) -> begin
Microsoft_FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta = (fun c mt -> (match (mt) with
| (Microsoft_FStar_Absyn_Syntax.Meta_pattern (t, _)) | (Microsoft_FStar_Absyn_Syntax.Meta_named (t, _)) | (Microsoft_FStar_Absyn_Syntax.Meta_labeled (t, _, _, _)) | (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (t, _, _)) | (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (t, _, _)) -> begin
(extractTyp c t)
end))
and extractTyConstApp = (fun c ftv ags -> (match ((isTypeScheme ftv.Microsoft_FStar_Absyn_Syntax.v c)) with
| true -> begin
(let mlargs = (Microsoft_FStar_List.map (getTypeFromArg c) ags)
in (let k = ftv.Microsoft_FStar_Absyn_Syntax.sort
in (let ar = (argIsExp k ftv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (let _62_198 = (Microsoft_FStar_Util.first_N (Microsoft_FStar_List.length mlargs) ar)
in (match (_62_198) with
| (_62_196, missingArgs) -> begin
(let argCompletion = (Microsoft_FStar_List.map mlty_of_isExp missingArgs)
in (let _128_98 = (let _128_97 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.Microsoft_FStar_Absyn_Syntax.v)
in ((Microsoft_FStar_List.append mlargs argCompletion), _128_97))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (_128_98)))
end)))))
end
| false -> begin
(All.failwith "this case was not anticipated")
end))
and extractBinderType = (fun c bn -> (match (bn) with
| (Microsoft_FStar_Util.Inl (btv), _62_205) -> begin
(let _128_102 = (extractKind c btv.Microsoft_FStar_Absyn_Syntax.sort)
in (let _128_101 = (extendContextAsTyvar false (Microsoft_FStar_Util.Inl (btv)) c)
in (_128_102, _128_101)))
end
| (Microsoft_FStar_Util.Inr (bvv), _62_210) -> begin
(let _128_104 = (extractTyp c bvv.Microsoft_FStar_Absyn_Syntax.sort)
in (let _128_103 = (extendContextAsTyvar false (Microsoft_FStar_Util.Inr (bvv)) c)
in (_128_104, _128_103)))
end))
and extractBindersTypes = (fun c bs -> (let _128_110 = (Microsoft_FStar_List.fold_left (fun _62_216 b -> (match (_62_216) with
| (lt, cp) -> begin
(let _62_220 = (extractBinderType cp b)
in (match (_62_220) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun _62_223 -> (match (_62_223) with
| (x, c) -> begin
((Microsoft_FStar_List.rev x), c)
end)) _128_110)))
and extractKind = (fun c ft -> Microsoft_FStar_Extraction_ML_Env.erasedContent)
and extractComp = (fun c ft -> (extractComp' c ft.Microsoft_FStar_Absyn_Syntax.n))
and extractComp' = (fun c ft -> (match (ft) with
| Microsoft_FStar_Absyn_Syntax.Total (ty) -> begin
(let _128_117 = (extractTyp c ty)
in (_128_117, Microsoft_FStar_Extraction_ML_Syntax.E_PURE))
end
| Microsoft_FStar_Absyn_Syntax.Comp (cm) -> begin
(let _128_119 = (extractTyp c cm.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _128_118 = (translate_eff c cm.Microsoft_FStar_Absyn_Syntax.effect_name)
in (_128_119, _128_118)))
end))

let binderPPnames = (fun bn -> (match (bn) with
| (Microsoft_FStar_Util.Inl (btv), _62_238) -> begin
btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end
| (Microsoft_FStar_Util.Inr (bvv), _62_243) -> begin
bvv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end))

let binderRealnames = (fun bn -> (match (bn) with
| (Microsoft_FStar_Util.Inl (btv), _62_249) -> begin
btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname
end
| (Microsoft_FStar_Util.Inr (bvv), _62_254) -> begin
bvv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname
end))

let mlsymbolOfLident = (fun id -> id.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)

type inductiveConstructor =
{cname : Microsoft_FStar_Absyn_Syntax.lident; ctype : Microsoft_FStar_Absyn_Syntax.typ}

let is_MkinductiveConstructor = (fun _ -> (All.failwith "Not yet implemented:is_MkinductiveConstructor"))

type inductiveTypeFam =
{tyName : Microsoft_FStar_Absyn_Syntax.lident; k : Microsoft_FStar_Absyn_Syntax.knd; tyBinders : Microsoft_FStar_Absyn_Syntax.binders; constructors : inductiveConstructor Prims.list; qualifiers : Microsoft_FStar_Absyn_Syntax.qualifier Prims.list}

let is_MkinductiveTypeFam = (fun _ -> (All.failwith "Not yet implemented:is_MkinductiveTypeFam"))

type typeAbbrev =
{abTyName : Microsoft_FStar_Absyn_Syntax.lident; abTyBinders : Microsoft_FStar_Absyn_Syntax.binders; abBody : Microsoft_FStar_Absyn_Syntax.typ}

let is_MktypeAbbrev = (fun _ -> (All.failwith "Not yet implemented:is_MktypeAbbrev"))

let lookupDataConType = (fun c sigb l -> (let tr = (Microsoft_FStar_Util.find_map sigb (fun s -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (l', t, tc, quals, lids, _62_280) -> begin
(match ((l = l')) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _62_284 -> begin
None
end)))
in (Microsoft_FStar_Util.must tr)))

let parseInductiveConstructors = (fun c cnames sigb -> (Microsoft_FStar_List.map (fun h -> (let _128_173 = (lookupDataConType c sigb h)
in {cname = h; ctype = _128_173})) cnames))

let rec parseInductiveTypesFromSigBundle = (fun c sigs -> (match (sigs) with
| [] -> begin
([], [], [])
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (l, bs, kk, _62_298, constrs, qs, _62_302)::tlsig -> begin
(let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (let _62_310 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_62_310) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (l, t, tc, quals, lids, _62_318)::tlsig -> begin
(match ((Microsoft_FStar_List.contains Microsoft_FStar_Absyn_Syntax.ExceptionConstructor quals)) with
| true -> begin
(let t = (Microsoft_FStar_Tc_Env.lookup_datacon c.Microsoft_FStar_Extraction_ML_Env.tcenv l)
in (let _62_323 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end
| false -> begin
([], [], [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _62_329, t, _62_332, _62_334)::tlsig -> begin
(let _62_341 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_62_341) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _128_179 = (let _128_178 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Microsoft_FStar_Util.format1 "unexpected content in a  sig bundle : %s\n" _128_178))
in (All.failwith _128_179))
end))

let rec argTypes = (fun t -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (a, _62_348, b) -> begin
(let _128_182 = (argTypes b)
in (a)::_128_182)
end
| _62_353 -> begin
[]
end))

let lident2mlsymbol = (fun l -> l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)

let totalType_of_comp = (fun ft -> (match (ft.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _62_359 -> begin
(All.failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

let allBindersOfFuntype = (fun c t -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
lb
end
| _62_368 -> begin
[]
end)))

let bindersOfFuntype = (fun c n t -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (lb, cp) -> begin
(let _62_379 = (Microsoft_FStar_Util.first_N n lb)
in (match (_62_379) with
| (ll, lr) -> begin
(match ((Microsoft_FStar_List.isEmpty lr)) with
| true -> begin
(let _128_197 = (totalType_of_comp cp)
in (ll, _128_197))
end
| false -> begin
(let _128_198 = (Microsoft_FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _128_198))
end)
end))
end
| _62_381 -> begin
(let _62_382 = ()
in ([], t))
end)))

let rec zipUnequal = (fun la lb -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _128_203 = (zipUnequal ta tb)
in ((ha, hb))::_128_203)
end
| _62_396 -> begin
[]
end))

let mlTyIdentOfBinder = (fun b -> (Microsoft_FStar_Extraction_ML_Env.prependTick (Microsoft_FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

let extractCtor = (fun tyBinders c ctor -> (let _62_403 = (bindersOfFuntype c (Microsoft_FStar_List.length tyBinders) ctor.ctype)
in (match (_62_403) with
| (lb, tr) -> begin
(let _62_404 = ()
in (let lp = (Microsoft_FStar_List.zip tyBinders lb)
in (let newC = (let _128_213 = (Microsoft_FStar_List.map (fun _62_409 -> (match (_62_409) with
| (x, y) -> begin
((Prims.fst x), (Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _128_213 c))
in (let mlt = (let _128_214 = (extractTyp newC tr)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep c _128_214))
in (let tys = (let _128_215 = (Microsoft_FStar_List.map mlTyIdentOfBinder tyBinders)
in (_128_215, mlt))
in (let fvv = (Microsoft_FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _128_218 = (Microsoft_FStar_Extraction_ML_Env.extend_fv c fvv tys false)
in (let _128_217 = (let _128_216 = (argTypes mlt)
in ((lident2mlsymbol ctor.cname), _128_216))
in (_128_218, _128_217)))))))))
end)))

let rec firstNNats = (fun n -> (match ((0 < n)) with
| true -> begin
(let _128_221 = (firstNNats (n - 1))
in (n)::_128_221)
end
| false -> begin
[]
end))

let dummyIdent = (fun n -> (let _128_225 = (let _128_224 = (Microsoft_FStar_Util.string_of_int n)
in (Prims.strcat "\'dummyV" _128_224))
in (_128_225, 0)))

let dummyIndexIdents = (fun n -> (let _128_228 = (firstNNats n)
in (Microsoft_FStar_List.map dummyIdent _128_228)))

let extractInductive = (fun c ind -> (let newContext = c
in (let nIndices = (numIndices ind.k ind.tyName.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let _62_423 = (Microsoft_FStar_Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_62_423) with
| (nc, tyb) -> begin
(let mlbs = (let _128_234 = (Microsoft_FStar_List.map mlTyIdentOfBinder ind.tyBinders)
in (let _128_233 = (dummyIndexIdents nIndices)
in (Microsoft_FStar_List.append _128_234 _128_233)))
in (let tbody = (match ((Microsoft_FStar_Util.find_opt (fun _62_1 -> (match (_62_1) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_62_427) -> begin
true
end
| _62_430 -> begin
false
end)) ind.qualifiers)) with
| Some (Microsoft_FStar_Absyn_Syntax.RecordType (ids)) -> begin
(let _62_434 = ()
in (let _62_439 = (Microsoft_FStar_List.hd tyb)
in (match (_62_439) with
| (_62_437, c_ty) -> begin
(let _62_440 = ()
in (let fields = (Microsoft_FStar_List.map2 (fun lid ty -> (lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, ty)) ids c_ty)
in Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _62_446 -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

let mfst = (fun x -> (Microsoft_FStar_List.map Prims.fst x))

let rec headBinders = (fun c t -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _62_459 = (let _128_244 = (let _128_243 = (mfst bs)
in (extendContext c _128_243))
in (headBinders _128_244 t))
in (match (_62_459) with
| (c, rb, rresidualType) -> begin
(c, (Microsoft_FStar_List.append bs rb), rresidualType)
end))
end
| _62_461 -> begin
(c, [], t)
end)))

let extractTypeAbbrev = (fun c tyab -> (let bs = tyab.abTyBinders
in (let t = tyab.abBody
in (let l = tyab.abTyName
in (let c = (let _128_249 = (mfst bs)
in (extendContext c _128_249))
in (let _62_471 = (headBinders c t)
in (match (_62_471) with
| (c, headBinders, residualType) -> begin
(let bs = (Microsoft_FStar_List.append bs headBinders)
in (let t = residualType
in (let mlt = (extractTyp c t)
in (let mlt = (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tyDecBody = Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (mlt)
in (let td = (let _128_250 = (Microsoft_FStar_List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _128_250, Some (tyDecBody)))
in (let c = (Microsoft_FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
in (c, td))))))))
end)))))))

let extractExn = (fun c exnConstr -> (let mlt = (extractTyp c exnConstr.ctype)
in (let mlt = (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep c mlt)
in (let tys = ([], mlt)
in (let fvv = (Microsoft_FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (let ex_decl = (let _128_256 = (let _128_255 = (argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _128_255))
in Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn (_128_256))
in (let _128_257 = (Microsoft_FStar_Extraction_ML_Env.extend_fv c fvv tys false)
in (_128_257, ex_decl))))))))

let rec extractSigElt = (fun c s -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, _62_491, t, _62_494, _62_496) -> begin
(let _62_501 = (extractTypeAbbrev c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_62_501) with
| (c, tds) -> begin
(c, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (sigs, Microsoft_FStar_Absyn_Syntax.ExceptionConstructor::[], _62_506, _62_508) -> begin
(let _62_516 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_62_516) with
| (_62_512, _62_514, exConstrs) -> begin
(let _62_517 = ()
in (let _62_521 = (let _128_262 = (Microsoft_FStar_List.hd exConstrs)
in (extractExn c _128_262))
in (match (_62_521) with
| (c, exDecl) -> begin
(c, (exDecl)::[])
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (sigs, _62_524, _62_526, _62_528) -> begin
(let _62_535 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_62_535) with
| (inds, abbs, _62_534) -> begin
(let _62_538 = (Microsoft_FStar_Util.fold_map extractInductive c inds)
in (match (_62_538) with
| (c, indDecls) -> begin
(let _62_541 = (Microsoft_FStar_Util.fold_map extractTypeAbbrev c abbs)
in (match (_62_541) with
| (c, tyAbDecls) -> begin
(c, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty ((Microsoft_FStar_List.append indDecls tyAbDecls)))::[])
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_62_543, _62_545, _62_547, _62_549, _62_551, quals, _62_554) -> begin
(match (((All.pipe_right quals (Microsoft_FStar_List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) && (not ((All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _62_2 -> (match (_62_2) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _62_565 -> begin
false
end)))))))) with
| true -> begin
(extractSigElt c (Microsoft_FStar_Absyn_Syntax.Sig_bundle (((s)::[], (Microsoft_FStar_Absyn_Syntax.Assumption)::[], [], (Microsoft_FStar_Absyn_Util.range_of_sigelt s)))))
end
| false -> begin
(c, [])
end)
end
| _62_567 -> begin
(c, [])
end))




