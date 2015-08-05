
let binderIsExp = (fun ( bn ) -> (Microsoft_FStar_Absyn_Print.is_inr (Support.Prims.fst bn)))

let rec argIsExp = (fun ( k ) ( typeName ) -> (match ((let _68_24894 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _68_24894.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, r)) -> begin
(let _68_24896 = (Support.List.map binderIsExp bs)
in (let _68_24895 = (argIsExp r typeName)
in (Support.List.append _68_24896 _68_24895)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k, _58_13, _58_15)) -> begin
(failwith ("extraction.numIndices : expected a compressed argument"))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_58_19, k)) -> begin
(argIsExp k typeName)
end
| _58_24 -> begin
(failwith ((Support.String.strcat "unexpected signature of inductive type" typeName)))
end))

let numIndices = (fun ( k ) ( typeName ) -> (let _68_24901 = (argIsExp k typeName)
in (Support.List.length _68_24901)))

let mlty_of_isExp = (fun ( b ) -> (match (b) with
| true -> begin
Microsoft_FStar_Extraction_ML_Env.erasedContent
end
| false -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end))

let delta_norm_eff = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (let rec delta_norm_eff = (fun ( g ) ( l ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find cache l.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(let res = (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev g.Microsoft_FStar_Extraction_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some ((_58_37, c)) -> begin
(delta_norm_eff g (Microsoft_FStar_Absyn_Util.comp_effect_name c))
end)
in (let _58_42 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str res)
in res))
end))
in delta_norm_eff))

let translate_eff = (fun ( g ) ( l ) -> (let l = (delta_norm_eff g l)
in (match (((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_PURE
end
| false -> begin
Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE
end)))

let rec curry = (fun ( inp ) ( f ) ( out ) -> (match (inp) with
| [] -> begin
out
end
| h::[] -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((h, f, out))
end
| h1::h2::tl -> begin
(let _68_24921 = (let _68_24920 = (curry ((h2)::tl) f out)
in (h1, Microsoft_FStar_Extraction_ML_Syntax.E_PURE, _68_24920))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_68_24921))
end))

type context =
Microsoft_FStar_Extraction_ML_Env.env

let extendContextWithRepAsTyVar = (fun ( b ) ( c ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (bt), Support.Microsoft.FStar.Util.Inl (btr)) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_ty c btr (Some (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var ((Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar bt)))))
end
| (Support.Microsoft.FStar.Util.Inr (bv), Support.Microsoft.FStar.Util.Inr (_58_68)) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_bv c bv ([], Microsoft_FStar_Extraction_ML_Env.erasedContent) false)
end
| _58_72 -> begin
(failwith ("Impossible case"))
end))

let extendContextWithRepAsTyVars = (fun ( b ) ( c ) -> (Support.List.fold_right extendContextWithRepAsTyVar b c))

let extendContextAsTyvar = (fun ( availableInML ) ( b ) ( c ) -> (match (b) with
| Support.Microsoft.FStar.Util.Inl (bt) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_ty c bt (Some ((match (availableInML) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var ((Microsoft_FStar_Extraction_ML_Env.btvar_as_mltyvar bt))
end
| false -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end))))
end
| Support.Microsoft.FStar.Util.Inr (bv) -> begin
(Microsoft_FStar_Extraction_ML_Env.extend_bv c bv ([], Microsoft_FStar_Extraction_ML_Env.erasedContent) false)
end))

let extendContext = (fun ( c ) ( tyVars ) -> (Support.List.fold_right (extendContextAsTyvar true) tyVars c))

let isTypeScheme = (fun ( i ) ( c ) -> true)

let preProcType = (fun ( c ) ( ft ) -> (let ft = (Microsoft_FStar_Absyn_Util.compress_typ ft)
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) c.Microsoft_FStar_Extraction_ML_Env.tcenv ft)))

let extractTyVar = (fun ( c ) ( btv ) -> (Microsoft_FStar_Extraction_ML_Env.lookup_tyvar c btv))

let rec extractTyp = (fun ( c ) ( ft ) -> (let ft = (preProcType c ft)
in (match (ft.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, codomain)) -> begin
(let _58_104 = (extractBindersTypes c bs)
in (match (_58_104) with
| (bts, newC) -> begin
(let _58_107 = (extractComp newC codomain)
in (match (_58_107) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((bv, _58_110)) -> begin
(extractTyp c bv.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((ty, arrgs)) -> begin
(let ty = (preProcType c ty)
in (let res = (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((tyin, argsin)) -> begin
(let _68_24973 = (Microsoft_FStar_Extraction_ML_Util.mkTypApp tyin (Support.List.append argsin arrgs) ty)
in (extractTyp c _68_24973))
end
| _58_127 -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end)
in res))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, ty)) -> begin
(let _58_135 = (extractBindersTypes c bs)
in (match (_58_135) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _58_138)) -> begin
(extractTyp c ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (mt) -> begin
(extractMeta c mt)
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_58_144) -> begin
Microsoft_FStar_Extraction_ML_Env.unknownType
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_58_147) -> begin
(failwith ("expected the argument to be compressed"))
end
| _58_150 -> begin
(failwith ("NYI. replace this with unknownType if you know the consequences"))
end)))
and getTypeFromArg = (fun ( c ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (ty) -> begin
(extractTyp c ty)
end
| Support.Microsoft.FStar.Util.Inr (_58_156) -> begin
Microsoft_FStar_Extraction_ML_Env.erasedContent
end))
and extractMeta = (fun ( c ) ( mt ) -> (match (mt) with
| (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _))) | (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t, _, _))) -> begin
(extractTyp c t)
end))
and extractTyConstApp = (fun ( c ) ( ftv ) ( ags ) -> (match ((isTypeScheme ftv.Microsoft_FStar_Absyn_Syntax.v c)) with
| true -> begin
(let mlargs = (Support.List.map (getTypeFromArg c) ags)
in (let k = ftv.Microsoft_FStar_Absyn_Syntax.sort
in (let ar = (argIsExp k ftv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (let _58_198 = (Support.Microsoft.FStar.Util.first_N (Support.List.length mlargs) ar)
in (match (_58_198) with
| (_58_196, missingArgs) -> begin
(let argCompletion = (Support.List.map mlty_of_isExp missingArgs)
in (let _68_24985 = (let _68_24984 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident ftv.Microsoft_FStar_Absyn_Syntax.v)
in ((Support.List.append mlargs argCompletion), _68_24984))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (_68_24985)))
end)))))
end
| false -> begin
(failwith ("this case was not anticipated"))
end))
and extractBinderType = (fun ( c ) ( bn ) -> (match (bn) with
| (Support.Microsoft.FStar.Util.Inl (btv), _58_205) -> begin
(let _68_24989 = (extractKind c btv.Microsoft_FStar_Absyn_Syntax.sort)
in (let _68_24988 = (extendContextAsTyvar false (Support.Microsoft.FStar.Util.Inl (btv)) c)
in (_68_24989, _68_24988)))
end
| (Support.Microsoft.FStar.Util.Inr (bvv), _58_210) -> begin
(let _68_24991 = (extractTyp c bvv.Microsoft_FStar_Absyn_Syntax.sort)
in (let _68_24990 = (extendContextAsTyvar false (Support.Microsoft.FStar.Util.Inr (bvv)) c)
in (_68_24991, _68_24990)))
end))
and extractBindersTypes = (fun ( c ) ( bs ) -> (let _68_24997 = (Support.List.fold_left (fun ( _58_216 ) ( b ) -> (match (_58_216) with
| (lt, cp) -> begin
(let _58_220 = (extractBinderType cp b)
in (match (_58_220) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)
in ((fun ( _58_223 ) -> (match (_58_223) with
| (x, c) -> begin
((Support.List.rev x), c)
end)) _68_24997)))
and extractKind = (fun ( c ) ( ft ) -> Microsoft_FStar_Extraction_ML_Env.erasedContent)
and extractComp = (fun ( c ) ( ft ) -> (extractComp' c ft.Microsoft_FStar_Absyn_Syntax.n))
and extractComp' = (fun ( c ) ( ft ) -> (match (ft) with
| Microsoft_FStar_Absyn_Syntax.Total (ty) -> begin
(let _68_25004 = (extractTyp c ty)
in (_68_25004, Microsoft_FStar_Extraction_ML_Syntax.E_PURE))
end
| Microsoft_FStar_Absyn_Syntax.Comp (cm) -> begin
(let _68_25006 = (extractTyp c cm.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _68_25005 = (translate_eff c cm.Microsoft_FStar_Absyn_Syntax.effect_name)
in (_68_25006, _68_25005)))
end))

let binderPPnames = (fun ( bn ) -> (match (bn) with
| (Support.Microsoft.FStar.Util.Inl (btv), _58_238) -> begin
btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end
| (Support.Microsoft.FStar.Util.Inr (bvv), _58_243) -> begin
bvv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end))

let binderRealnames = (fun ( bn ) -> (match (bn) with
| (Support.Microsoft.FStar.Util.Inl (btv), _58_249) -> begin
btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname
end
| (Support.Microsoft.FStar.Util.Inr (bvv), _58_254) -> begin
bvv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname
end))

let mlsymbolOfLident = (fun ( id ) -> id.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)

type inductiveConstructor =
{cname : Microsoft_FStar_Absyn_Syntax.lident; ctype : Microsoft_FStar_Absyn_Syntax.typ}

let is_MkinductiveConstructor = (fun ( _ ) -> (failwith ("Not yet implemented:is_MkinductiveConstructor")))

type inductiveTypeFam =
{tyName : Microsoft_FStar_Absyn_Syntax.lident; k : Microsoft_FStar_Absyn_Syntax.knd; tyBinders : Microsoft_FStar_Absyn_Syntax.binders; constructors : inductiveConstructor list; qualifiers : Microsoft_FStar_Absyn_Syntax.qualifier list}

let is_MkinductiveTypeFam = (fun ( _ ) -> (failwith ("Not yet implemented:is_MkinductiveTypeFam")))

type typeAbbrev =
{abTyName : Microsoft_FStar_Absyn_Syntax.lident; abTyBinders : Microsoft_FStar_Absyn_Syntax.binders; abBody : Microsoft_FStar_Absyn_Syntax.typ}

let is_MktypeAbbrev = (fun ( _ ) -> (failwith ("Not yet implemented:is_MktypeAbbrev")))

let lookupDataConType = (fun ( c ) ( sigb ) ( l ) -> (let tr = (Support.Microsoft.FStar.Util.find_map sigb (fun ( s ) -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((l', t, tc, quals, lids, _58_280)) -> begin
(match ((l = l')) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _58_284 -> begin
None
end)))
in (Support.Microsoft.FStar.Util.must tr)))

let parseInductiveConstructors = (fun ( c ) ( cnames ) ( sigb ) -> (Support.List.map (fun ( h ) -> (let _68_25060 = (lookupDataConType c sigb h)
in {cname = h; ctype = _68_25060})) cnames))

let rec parseInductiveTypesFromSigBundle = (fun ( c ) ( sigs ) -> (match (sigs) with
| [] -> begin
([], [], [])
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((l, bs, kk, _58_298, constrs, qs, _58_302))::tlsig -> begin
(let indConstrs = (parseInductiveConstructors c constrs tlsig)
in (let _58_310 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_58_310) with
| (inds, abbs, exns) -> begin
(({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs; qualifiers = qs})::inds, abbs, exns)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((l, t, tc, quals, lids, _58_318))::tlsig -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.ExceptionConstructor quals)) with
| true -> begin
(let t = (Microsoft_FStar_Tc_Env.lookup_datacon c.Microsoft_FStar_Extraction_ML_Env.tcenv l)
in (let _58_323 = ()
in ([], [], ({cname = l; ctype = t})::[])))
end
| false -> begin
([], [], [])
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((l, bs, _58_329, t, _58_332, _58_334))::tlsig -> begin
(let _58_341 = (parseInductiveTypesFromSigBundle c tlsig)
in (match (_58_341) with
| (inds, abbs, exns) -> begin
(inds, ({abTyName = l; abTyBinders = bs; abBody = t})::abbs, exns)
end))
end
| se::tlsig -> begin
(let _68_25066 = (let _68_25065 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "unexpected content in a  sig bundle : %s\n" _68_25065))
in (failwith (_68_25066)))
end))

let rec argTypes = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((a, _58_348, b)) -> begin
(let _68_25069 = (argTypes b)
in (a)::_68_25069)
end
| _58_353 -> begin
[]
end))

let lident2mlsymbol = (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)

let totalType_of_comp = (fun ( ft ) -> (match (ft.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _58_359 -> begin
(failwith ("expected a total type. constructors of inductive types were assumed to be total"))
end))

let allBindersOfFuntype = (fun ( c ) ( t ) -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((lb, cp)) -> begin
lb
end
| _58_368 -> begin
[]
end)))

let bindersOfFuntype = (fun ( c ) ( n ) ( t ) -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((lb, cp)) -> begin
(let _58_379 = (Support.Microsoft.FStar.Util.first_N n lb)
in (match (_58_379) with
| (ll, lr) -> begin
(match ((Support.List.isEmpty lr)) with
| true -> begin
(let _68_25084 = (totalType_of_comp cp)
in (ll, _68_25084))
end
| false -> begin
(let _68_25085 = (Microsoft_FStar_Extraction_ML_Util.mkTypFun lr cp t)
in (ll, _68_25085))
end)
end))
end
| _58_381 -> begin
(let _58_382 = ()
in ([], t))
end)))

let rec zipUnequal = (fun ( la ) ( lb ) -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
(let _68_25090 = (zipUnequal ta tb)
in ((ha, hb))::_68_25090)
end
| _58_396 -> begin
[]
end))

let mlTyIdentOfBinder = (fun ( b ) -> (Microsoft_FStar_Extraction_ML_Env.prependTick (Microsoft_FStar_Extraction_ML_Env.convIdent (binderPPnames b))))

let extractCtor = (fun ( tyBinders ) ( c ) ( ctor ) -> (let _58_403 = (bindersOfFuntype c (Support.List.length tyBinders) ctor.ctype)
in (match (_58_403) with
| (lb, tr) -> begin
(let _58_404 = ()
in (let lp = (Support.List.zip tyBinders lb)
in (let newC = (let _68_25100 = (Support.List.map (fun ( _58_409 ) -> (match (_58_409) with
| (x, y) -> begin
((Support.Prims.fst x), (Support.Prims.fst y))
end)) lp)
in (extendContextWithRepAsTyVars _68_25100 c))
in (let mlt = (let _68_25101 = (extractTyp newC tr)
in (Microsoft_FStar_Extraction_ML_Util.eraseTypeDeep c _68_25101))
in (let tys = (let _68_25102 = (Support.List.map mlTyIdentOfBinder tyBinders)
in (_68_25102, mlt))
in (let fvv = (Microsoft_FStar_Extraction_ML_Env.mkFvvar ctor.cname ctor.ctype)
in (let _68_25105 = (Microsoft_FStar_Extraction_ML_Env.extend_fv c fvv tys false)
in (let _68_25104 = (let _68_25103 = (argTypes mlt)
in ((lident2mlsymbol ctor.cname), _68_25103))
in (_68_25105, _68_25104)))))))))
end)))

let rec firstNNats = (fun ( n ) -> (match ((0 < n)) with
| true -> begin
(let _68_25108 = (firstNNats (n - 1))
in (n)::_68_25108)
end
| false -> begin
[]
end))

let dummyIdent = (fun ( n ) -> (let _68_25112 = (let _68_25111 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.String.strcat "\'dummyV" _68_25111))
in (_68_25112, 0)))

let dummyIndexIdents = (fun ( n ) -> (let _68_25115 = (firstNNats n)
in (Support.List.map dummyIdent _68_25115)))

let extractInductive = (fun ( c ) ( ind ) -> (let newContext = c
in (let nIndices = (numIndices ind.k ind.tyName.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let _58_423 = (Support.Microsoft.FStar.Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_58_423) with
| (nc, tyb) -> begin
(let mlbs = (let _68_25121 = (Support.List.map mlTyIdentOfBinder ind.tyBinders)
in (let _68_25120 = (dummyIndexIdents nIndices)
in (Support.List.append _68_25121 _68_25120)))
in (let tbody = (match ((Support.Microsoft.FStar.Util.find_opt (fun ( _58_1 ) -> (match (_58_1) with
| Microsoft_FStar_Absyn_Syntax.RecordType (_58_427) -> begin
true
end
| _58_430 -> begin
false
end)) ind.qualifiers)) with
| Some (Microsoft_FStar_Absyn_Syntax.RecordType (ids)) -> begin
(let _58_434 = ()
in (let _58_439 = (Support.List.hd tyb)
in (match (_58_439) with
| (_58_437, c_ty) -> begin
(let _58_440 = ()
in (let fields = (Support.List.map2 (fun ( lid ) ( ty ) -> (lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, ty)) ids c_ty)
in Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end)))
end
| _58_446 -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (tyb)
end)
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (tbody)))))
end)))))

let mfst = (fun ( x ) -> (Support.List.map Support.Prims.fst x))

let rec headBinders = (fun ( c ) ( t ) -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _58_459 = (let _68_25131 = (let _68_25130 = (mfst bs)
in (extendContext c _68_25130))
in (headBinders _68_25131 t))
in (match (_58_459) with
| (c, rb, rresidualType) -> begin
(c, (Support.List.append bs rb), rresidualType)
end))
end
| _58_461 -> begin
(c, [], t)
end)))

let extractTypeAbbrev = (fun ( c ) ( tyab ) -> (let bs = tyab.abTyBinders
in (let t = tyab.abBody
in (let l = tyab.abTyName
in (let c = (let _68_25136 = (mfst bs)
in (extendContext c _68_25136))
in (let _58_471 = (headBinders c t)
in (match (_58_471) with
| (c, headBinders, residualType) -> begin
(let bs = (Support.List.append bs headBinders)
in (let t = residualType
in (let tyDecBody = (let _68_25137 = (extractTyp c t)
in Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (_68_25137))
in (let td = (let _68_25138 = (Support.List.map mlTyIdentOfBinder bs)
in ((mlsymbolOfLident l), _68_25138, Some (tyDecBody)))
in (let c = (Microsoft_FStar_Extraction_ML_Env.extend_tydef c ((td)::[]))
in (c, td))))))
end)))))))

let extractExn = (fun ( c ) ( exnConstr ) -> (let mlt = (extractTyp c exnConstr.ctype)
in (let tys = ([], mlt)
in (let fvv = (Microsoft_FStar_Extraction_ML_Env.mkFvvar exnConstr.cname exnConstr.ctype)
in (let ex_decl = (let _68_25144 = (let _68_25143 = (argTypes mlt)
in ((lident2mlsymbol exnConstr.cname), _68_25143))
in Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn (_68_25144))
in (let _68_25145 = (Microsoft_FStar_Extraction_ML_Env.extend_fv c fvv tys false)
in (_68_25145, ex_decl)))))))

let rec extractSigElt = (fun ( c ) ( s ) -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((l, bs, _58_488, t, _58_491, _58_493)) -> begin
(let _58_498 = (extractTypeAbbrev c {abTyName = l; abTyBinders = bs; abBody = t})
in (match (_58_498) with
| (c, tds) -> begin
(c, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty ((tds)::[]))::[])
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, Microsoft_FStar_Absyn_Syntax.ExceptionConstructor::[], _58_503, _58_505)) -> begin
(let _58_513 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_58_513) with
| (_58_509, _58_511, exConstrs) -> begin
(let _58_514 = ()
in (let _58_518 = (let _68_25150 = (Support.List.hd exConstrs)
in (extractExn c _68_25150))
in (match (_58_518) with
| (c, exDecl) -> begin
(c, (exDecl)::[])
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _58_521, _58_523, _58_525)) -> begin
(let _58_532 = (parseInductiveTypesFromSigBundle c sigs)
in (match (_58_532) with
| (inds, abbs, _58_531) -> begin
(let _58_535 = (Support.Microsoft.FStar.Util.fold_map extractInductive c inds)
in (match (_58_535) with
| (c, indDecls) -> begin
(let _58_538 = (Support.Microsoft.FStar.Util.fold_map extractTypeAbbrev c abbs)
in (match (_58_538) with
| (c, tyAbDecls) -> begin
(c, (Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty ((Support.List.append indDecls tyAbDecls)))::[])
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_58_540, _58_542, _58_544, _58_546, _58_548, quals, _58_551)) -> begin
(match (((Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) && (not ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _58_2 ) -> (match (_58_2) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _58_562 -> begin
false
end)))))))) with
| true -> begin
(extractSigElt c (Microsoft_FStar_Absyn_Syntax.Sig_bundle (((s)::[], (Microsoft_FStar_Absyn_Syntax.Assumption)::[], [], (Microsoft_FStar_Absyn_Util.range_of_sigelt s)))))
end
| false -> begin
(c, [])
end)
end
| _58_564 -> begin
(c, [])
end))




