
let binderIsExp = (fun ( bn ) -> (Microsoft_FStar_Absyn_Print.is_inr (Support.Prims.fst bn)))

let rec argIsExp = (fun ( k ) ( typeName ) -> (match ((Microsoft_FStar_Absyn_Util.compress_kind k).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, r)) -> begin
(Support.List.append (Support.List.map binderIsExp bs) (argIsExp r typeName))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k, _, _)) -> begin
(failwith "extraction.numIndices : expected a compressed argument")
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(argIsExp k typeName)
end
| _ -> begin
(failwith (Support.String.strcat "unexpected signature of inductive type" typeName))
end))

let numIndices = (fun ( k ) ( typeName ) -> (Support.List.length (argIsExp k typeName)))

let mlty_of_isExp = (fun ( b ) -> if b then begin
Microsoft_FStar_Backends_ML_Env.erasedContent
end else begin
Microsoft_FStar_Backends_ML_Env.unknownType
end)

let delta_norm_eff = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (let rec delta_norm_eff = (fun ( g ) ( l ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find cache l.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(let res = (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev g.Microsoft_FStar_Backends_ML_Env.tcenv l)) with
| None -> begin
l
end
| Some ((_, c)) -> begin
(delta_norm_eff g (Microsoft_FStar_Absyn_Util.comp_effect_name c))
end)
in (let _53_41 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str res)
in res))
end))
in delta_norm_eff))

let translate_eff = (fun ( g ) ( l ) -> (let l = (delta_norm_eff g l)
in if (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) then begin
Microsoft_FStar_Backends_ML_Syntax.MayErase
end else begin
Microsoft_FStar_Backends_ML_Syntax.Keep
end))

let rec curry = (fun ( inp ) ( erase ) ( out ) -> (match (inp) with
| [] -> begin
out
end
| h::tl -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((h, erase, (curry tl erase out)))
end))

type context =
Microsoft_FStar_Backends_ML_Env.env

let extendContextWithRepAsTyVar = (fun ( b ) ( c ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (bt), Support.Microsoft.FStar.Util.Inl (btr)) -> begin
(Microsoft_FStar_Backends_ML_Env.extend_ty c btr (Some (Microsoft_FStar_Backends_ML_Syntax.MLTY_Var ((Microsoft_FStar_Backends_ML_Env.btvar_as_mlident bt)))))
end
| (Support.Microsoft.FStar.Util.Inr (bv), Support.Microsoft.FStar.Util.Inr (_)) -> begin
(Microsoft_FStar_Backends_ML_Env.extend_bv c bv ([], Microsoft_FStar_Backends_ML_Env.erasedContent))
end
| _ -> begin
(failwith "Impossible case")
end))

let extendContextWithRepAsTyVars = (fun ( b ) ( c ) -> (Support.List.fold_right extendContextWithRepAsTyVar b c))

let extendContextAsTyvar = (fun ( availableInML ) ( b ) ( c ) -> (match (b) with
| Support.Microsoft.FStar.Util.Inl (bt) -> begin
(Microsoft_FStar_Backends_ML_Env.extend_ty c bt (Some (if availableInML then begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Var ((Microsoft_FStar_Backends_ML_Env.btvar_as_mlident bt))
end else begin
Microsoft_FStar_Backends_ML_Env.unknownType
end)))
end
| Support.Microsoft.FStar.Util.Inr (bv) -> begin
(Microsoft_FStar_Backends_ML_Env.extend_bv c bv ([], Microsoft_FStar_Backends_ML_Env.erasedContent))
end))

let extendContext = (fun ( c ) ( tyVars ) -> (Support.List.fold_right (extendContextAsTyvar true) tyVars c))

let isTypeScheme = (fun ( i ) ( c ) -> true)

let preProcType = (fun ( c ) ( ft ) -> (let ft = (Microsoft_FStar_Absyn_Util.compress_typ ft)
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) c.Microsoft_FStar_Backends_ML_Env.tcenv ft)))

let extractTyVar = (fun ( c ) ( btv ) -> (Microsoft_FStar_Backends_ML_Env.lookup_ty c (Support.Microsoft.FStar.Util.Inl (btv))))

let rec extractTyp = (fun ( c ) ( ft ) -> (let ft = (preProcType c ft)
in (match (ft.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, codomain)) -> begin
(let _53_99 = (extractBindersTypes c bs)
in (match (_53_99) with
| (bts, newC) -> begin
(let _53_102 = (extractComp newC codomain)
in (match (_53_102) with
| (codomainML, erase) -> begin
(curry bts erase codomainML)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((bv, _)) -> begin
(extractTyp c bv.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((ty, arrgs)) -> begin
(let ty = (preProcType c ty)
in (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(extractTyVar c btv)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(extractTyConstApp c ftv arrgs)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((tyin, argsin)) -> begin
(extractTyp c (Microsoft_FStar_Backends_ML_Util.mkTypApp tyin (Support.List.append argsin arrgs) ty))
end
| _ -> begin
Microsoft_FStar_Backends_ML_Env.unknownType
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, ty)) -> begin
(let _53_129 = (extractBindersTypes c bs)
in (match (_53_129) with
| (bts, c) -> begin
(extractTyp c ty)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(extractTyp c ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_) -> begin
(failwith "NYI")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_) -> begin
(failwith "NYI")
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith "expected the argument to be compressed")
end
| _ -> begin
(failwith "NYI. replace this with unknownType if you know the consequences")
end)))
and getTypeFromArg = (fun ( c ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (ty) -> begin
(extractTyp c ty)
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
Microsoft_FStar_Backends_ML_Env.erasedContent
end))
and extractTyConstApp = (fun ( c ) ( ftv ) ( ags ) -> if (isTypeScheme ftv.Microsoft_FStar_Absyn_Syntax.v c) then begin
(let mlargs = (Support.List.map (getTypeFromArg c) ags)
in (let k = ftv.Microsoft_FStar_Absyn_Syntax.sort
in (let ar = (argIsExp k ftv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (let _53_163 = (Support.Microsoft.FStar.Util.first_N (Support.List.length mlargs) ar)
in (match (_53_163) with
| (_, missingArgs) -> begin
(let argCompletion = (Support.List.map mlty_of_isExp missingArgs)
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (((Support.List.append mlargs argCompletion), (Microsoft_FStar_Backends_ML_Env.mlpath_of_lident c.Microsoft_FStar_Backends_ML_Env.currentModule ftv.Microsoft_FStar_Absyn_Syntax.v))))
end)))))
end else begin
(failwith "this case was not anticipated")
end)
and extractBinderType = (fun ( c ) ( bn ) -> (match (bn) with
| (Support.Microsoft.FStar.Util.Inl (btv), _) -> begin
((extractKind c btv.Microsoft_FStar_Absyn_Syntax.sort), (extendContextAsTyvar false (Support.Microsoft.FStar.Util.Inl (btv)) c))
end
| (Support.Microsoft.FStar.Util.Inr (bvv), _) -> begin
((extractTyp c bvv.Microsoft_FStar_Absyn_Syntax.sort), (extendContextAsTyvar false (Support.Microsoft.FStar.Util.Inr (bvv)) c))
end))
and extractBindersTypes = (fun ( c ) ( bs ) -> ((fun ( _53_189 ) -> (match (_53_189) with
| (x, c) -> begin
((Support.List.rev x), c)
end)) (Support.List.fold_left (fun ( _53_182 ) ( b ) -> (match (_53_182) with
| (lt, cp) -> begin
(let _53_186 = (extractBinderType cp b)
in (match (_53_186) with
| (nt, nc) -> begin
((nt)::lt, nc)
end))
end)) ([], c) bs)))
and extractKind = (fun ( c ) ( ft ) -> Microsoft_FStar_Backends_ML_Env.erasedContent)
and extractComp = (fun ( c ) ( ft ) -> (extractComp' c ft.Microsoft_FStar_Absyn_Syntax.n))
and extractComp' = (fun ( c ) ( ft ) -> (match (ft) with
| Microsoft_FStar_Absyn_Syntax.Total (ty) -> begin
((extractTyp c ty), Microsoft_FStar_Backends_ML_Syntax.MayErase)
end
| Microsoft_FStar_Absyn_Syntax.Comp (cm) -> begin
((extractTyp c cm.Microsoft_FStar_Absyn_Syntax.result_typ), (translate_eff c cm.Microsoft_FStar_Absyn_Syntax.effect_name))
end))

let binderPPnames = (fun ( bn ) -> (match (bn) with
| (Support.Microsoft.FStar.Util.Inl (btv), _) -> begin
btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end
| (Support.Microsoft.FStar.Util.Inr (bvv), _) -> begin
bvv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end))

let binderRealnames = (fun ( bn ) -> (match (bn) with
| (Support.Microsoft.FStar.Util.Inl (btv), _) -> begin
btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname
end
| (Support.Microsoft.FStar.Util.Inr (bvv), _) -> begin
bvv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname
end))

let mlsymbolOfLident = (fun ( id ) -> id.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)

type inductiveConstructor =
{cname : Microsoft_FStar_Absyn_Syntax.lident; ctype : Microsoft_FStar_Absyn_Syntax.typ}

type inductiveTypeFam =
{tyName : Microsoft_FStar_Absyn_Syntax.lident; k : Microsoft_FStar_Absyn_Syntax.knd; tyBinders : Microsoft_FStar_Absyn_Syntax.binders; constructors : inductiveConstructor list}

let parseInductiveConstructors = (fun ( c ) ( cnames ) -> (Support.List.map (fun ( h ) -> {cname = h; ctype = (Microsoft_FStar_Tc_Env.lookup_datacon c.Microsoft_FStar_Backends_ML_Env.tcenv h)}) cnames))

let rec parseInductiveTypesFromSigBundle = (fun ( c ) ( sigs ) -> (match (sigs) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((l, bs, kk, _, constrs, _, _))::tlsig -> begin
(let indConstrs = (parseInductiveConstructors c constrs)
in ({tyName = l; k = kk; tyBinders = bs; constructors = indConstrs})::(parseInductiveTypesFromSigBundle c tlsig))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_)::tlsig -> begin
[]
end
| [] -> begin
[]
end
| se::tlsig -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "unexpected, or a type abbrev mutually defined with an inductive (NYI) : %s\n" (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)))
end))

let rec argTypes = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((a, _, b)) -> begin
(a)::(argTypes b)
end
| _ -> begin
[]
end))

let lident2mlsymbol = (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)

let totalType_of_comp = (fun ( ft ) -> (match (ft.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (ty) -> begin
ty
end
| _ -> begin
(failwith "expected a total type. constructors of inductive types were assumed to be total")
end))

let bindersOfFuntype = (fun ( c ) ( n ) ( t ) -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((lb, cp)) -> begin
(let _53_285 = (Support.Microsoft.FStar.Util.first_N n lb)
in (match (_53_285) with
| (ll, lr) -> begin
if (Support.List.isEmpty lr) then begin
(ll, (totalType_of_comp cp))
end else begin
(ll, (Microsoft_FStar_Backends_ML_Util.mkTypFun lr cp t))
end
end))
end
| _ -> begin
(let _53_288 = (Support.Prims._assert ())
in ([], t))
end)))

let rec zipUnequal = (fun ( la ) ( lb ) -> (match ((la, lb)) with
| (ha::ta, hb::tb) -> begin
((ha, hb))::(zipUnequal ta tb)
end
| _ -> begin
[]
end))

let mlTyIdentOfBinder = (fun ( b ) -> (Microsoft_FStar_Backends_ML_Env.prependTick (Microsoft_FStar_Backends_ML_Env.convIdent (binderPPnames b))))

let extractCtor = (fun ( tyBinders ) ( c ) ( ctor ) -> (let _53_309 = (bindersOfFuntype c (Support.List.length tyBinders) ctor.ctype)
in (match (_53_309) with
| (lb, tr) -> begin
(let _53_310 = (Support.Prims._assert ())
in (let lp = (Support.List.zip tyBinders lb)
in (let newC = (extendContextWithRepAsTyVars (Support.List.map (fun ( _53_315 ) -> (match (_53_315) with
| (x, y) -> begin
((Support.Prims.fst x), (Support.Prims.fst y))
end)) lp) c)
in (let mlt = (extractTyp newC tr)
in (let tys = ((Support.List.map mlTyIdentOfBinder tyBinders), mlt)
in (let fvv = (Microsoft_FStar_Backends_ML_Env.mkFvvar ctor.cname ctor.ctype)
in ((Microsoft_FStar_Backends_ML_Env.extend_fv c fvv tys), ((lident2mlsymbol ctor.cname), (argTypes mlt)))))))))
end)))

let dummyIdent = (fun ( n ) -> ((Support.String.strcat "\'dummyV" (Support.Microsoft.FStar.Util.string_of_int n)), 0))

let rec firstNNats = (fun ( n ) -> if (0 < n) then begin
(n)::(firstNNats (n - 1))
end else begin
[]
end)

let dummyIndexIdents = (fun ( n ) -> (Support.List.map dummyIdent (firstNNats n)))

let extractInductive = (fun ( c ) ( ind ) -> (let newContext = c
in (let nIndices = (numIndices ind.k ind.tyName.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let _53_329 = (Support.Microsoft.FStar.Util.fold_map (extractCtor ind.tyBinders) newContext ind.constructors)
in (match (_53_329) with
| (nc, tyb) -> begin
(let mlbs = (Support.List.append (Support.List.map mlTyIdentOfBinder ind.tyBinders) (dummyIndexIdents nIndices))
in (nc, ((lident2mlsymbol ind.tyName), mlbs, Some (Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (tyb)))))
end)))))

let mfst = (Support.List.map (Support.Prims.fst))

let rec headBinders = (fun ( c ) ( t ) -> (let t = (preProcType c t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _53_341 = (headBinders (extendContext c (mfst bs)) t)
in (match (_53_341) with
| (c, rb, rresidualType) -> begin
(c, (Support.List.append bs rb), rresidualType)
end))
end
| _ -> begin
(c, [], t)
end)))

let rec extractSigElt = (fun ( c ) ( s ) -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((l, bs, _, t, _, _)) -> begin
(let c = (extendContext c (mfst bs))
in (let _53_361 = (headBinders c t)
in (match (_53_361) with
| (c, headBinders, residualType) -> begin
(let bs = (Support.List.append bs headBinders)
in (let t = residualType
in (let tyDecBody = Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev ((extractTyp c t))
in (let td = (((mlsymbolOfLident l), (Support.List.map mlTyIdentOfBinder bs), Some (tyDecBody)))::[]
in (let c = (Microsoft_FStar_Backends_ML_Env.extend_tydef c td)
in (c, td))))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((sigs, _, _, _)) -> begin
(let inds = (parseInductiveTypesFromSigBundle c sigs)
in (Support.Microsoft.FStar.Util.fold_map extractInductive c inds))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, quals, _)) -> begin
if (((Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption) quals) && (not (((Support.Microsoft.FStar.Util.for_some (fun ( _53_1 ) -> (match (_53_1) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _ -> begin
false
end))) quals)))) then begin
(extractSigElt c (Microsoft_FStar_Absyn_Syntax.Sig_bundle (((s)::[], (Microsoft_FStar_Absyn_Syntax.Assumption)::[], [], (Microsoft_FStar_Absyn_Util.range_of_sigelt s)))))
end else begin
(c, [])
end
end
| _ -> begin
(c, [])
end))

let emptyMlPath = ([], "")

let mkContext = (fun ( e ) -> (let env = {Microsoft_FStar_Backends_ML_Env.tcenv = e; Microsoft_FStar_Backends_ML_Env.gamma = []; Microsoft_FStar_Backends_ML_Env.tydefs = []; Microsoft_FStar_Backends_ML_Env.erasableTypes = Microsoft_FStar_Backends_ML_Env.erasableType_init; Microsoft_FStar_Backends_ML_Env.currentModule = emptyMlPath}
in (let a = ("a", (- (1)))
in (let failwith_ty = ((a)::[], Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), Microsoft_FStar_Backends_ML_Syntax.Keep, Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (a))))
in ((Support.Prims.fst) (Microsoft_FStar_Backends_ML_Env.extend_lb env (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Const.failwith_lid)) Microsoft_FStar_Absyn_Syntax.tun failwith_ty))))))




