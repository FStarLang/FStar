
type mlenv =
{mle_name : Microsoft_FStar_Backends_ML_Syntax.mlpath}

let is_Mkmlenv = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkmlenv")))

let mk_mlenv = (fun ( name ) -> {mle_name = name})

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Set")::[])::(("Map")::[])::(("Heap")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let record_constructors = (Support.Microsoft.FStar.Util.smap_create 17)

let algebraic_constructors = (Support.Microsoft.FStar.Util.smap_create 40)

let _ign = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors "Prims.Some" (1, ("v")::[]))

let rec in_ns = (fun ( _67_1 ) -> (match (_67_1) with
| ([], _67_28) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(Obj.magic in_ns)
end
| (_67_38, _67_40) -> begin
false
end))

let path_of_ns = (fun ( mlenv ) ( ns ) -> (let ns = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) ns)
in (let outsupport = (fun ( _67_48 ) -> (match (_67_48) with
| (ns1, ns2) -> begin
(match ((ns1 = ns2)) with
| true -> begin
[]
end
| false -> begin
((Support.String.concat "_" ns2))::[]
end)
end))
in (let chkin = (fun ( sns ) -> (match ((in_ns (sns, ns))) with
| true -> begin
Some (sns)
end
| false -> begin
None
end))
in (match ((Support.List.tryPick chkin outmod)) with
| None -> begin
(match ((let _68_26309 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _68_26309))) with
| None -> begin
(outsupport ((Support.List.append (Support.Prims.fst mlenv.mle_name) (((Support.Prims.snd mlenv.mle_name))::[])), ns))
end
| _67_55 -> begin
ns
end)
end
| Some (sns) -> begin
("Support")::ns
end)))))

let mlpath_of_lident = (fun ( mlenv ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.str) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| "Prims.failwith" -> begin
([], "failwith")
end
| "ST.alloc" -> begin
([], "ref")
end
| "ST.read" -> begin
(("Support")::("Prims")::[], "op_Bang")
end
| "ST.op_ColonEquals" -> begin
(("Support")::("Prims")::[], "op_ColonEquals")
end
| _67_67 -> begin
(let ns = x.Microsoft_FStar_Absyn_Syntax.ns
in (let x = x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (let _68_26314 = (path_of_ns mlenv ns)
in (_68_26314, x))))
end))

type error =
| Unexpected of string
| Unsupported of string
| UnboundVar of string
| UnboundTyVar of string
| DuplicatedLocal of (string * string)

let is_Unexpected = (fun ( _discr_ ) -> (match (_discr_) with
| Unexpected (_) -> begin
true
end
| _ -> begin
false
end))

let is_Unsupported = (fun ( _discr_ ) -> (match (_discr_) with
| Unsupported (_) -> begin
true
end
| _ -> begin
false
end))

let is_UnboundVar = (fun ( _discr_ ) -> (match (_discr_) with
| UnboundVar (_) -> begin
true
end
| _ -> begin
false
end))

let is_UnboundTyVar = (fun ( _discr_ ) -> (match (_discr_) with
| UnboundTyVar (_) -> begin
true
end
| _ -> begin
false
end))

let is_DuplicatedLocal = (fun ( _discr_ ) -> (match (_discr_) with
| DuplicatedLocal (_) -> begin
true
end
| _ -> begin
false
end))

exception OCamlFailure of ((Support.Microsoft.FStar.Range.range * error))

let is_OCamlFailure = (fun ( _discr_ ) -> (match (_discr_) with
| OCamlFailure (_) -> begin
true
end
| _ -> begin
false
end))

let string_of_error = (fun ( error ) -> (match (error) with
| Unexpected (s) -> begin
(Support.String.strcat "unexpected: " s)
end
| Unsupported (s) -> begin
(Support.String.strcat "unsupported: " s)
end
| UnboundVar (s) -> begin
(Support.String.strcat "unbound-var: " s)
end
| UnboundTyVar (s) -> begin
(Support.String.strcat "unbound-ty-var: " s)
end
| DuplicatedLocal (_67_91) -> begin
"duplicated-local"
end))

let unexpected = (fun ( rg ) ( what ) -> (raise (OCamlFailure ((rg, Unexpected (what))))))

let unsupported = (fun ( rg ) ( what ) -> (raise (OCamlFailure ((rg, Unsupported (what))))))

let unbound_var = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, UnboundVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let unbound_ty_var = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, UnboundTyVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let duplicated_local = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, DuplicatedLocal (x))))))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( x ) -> (let _67_105 = (Support.Microsoft.FStar.Util.incr c)
in (let _68_26367 = (Support.ST.read c)
in (x, _68_26367)))))

let tyvar_of_int = (let tyvars = "abcdefghijklmnopqrstuvwxyz"
in (let rec aux = (fun ( n ) -> (let s = (let _68_26371 = (Support.String.get tyvars (n mod 26))
in (Support.Microsoft.FStar.Util.string_of_char _68_26371))
in (match ((n >= (Support.String.length tyvars))) with
| true -> begin
(let _68_26372 = (aux (n / 26))
in (Support.String.strcat _68_26372 s))
end
| false -> begin
s
end)))
in (fun ( n ) -> (let _68_26374 = (aux n)
in (Support.String.strcat "\'" _68_26374)))))

type lenv =
| LEnv of Microsoft_FStar_Backends_ML_Syntax.mlident Support.Microsoft.FStar.Util.smap

let is_LEnv = (fun ( _discr_ ) -> (match (_discr_) with
| LEnv (_) -> begin
true
end
| _ -> begin
false
end))

let lempty = (let _68_26379 = (Support.Microsoft.FStar.Util.smap_create 0)
in LEnv (_68_26379))

let lenv_of_mlenv = (fun ( _67_113 ) -> lempty)

let lpush = (fun ( _67_116 ) ( real ) ( pp ) -> (match (_67_116) with
| LEnv (lenv) -> begin
(let mlid = (fresh pp.Microsoft_FStar_Absyn_Syntax.idText)
in (let _67_120 = (Support.Microsoft.FStar.Util.smap_add lenv real.Microsoft_FStar_Absyn_Syntax.idText mlid)
in (LEnv (lenv), mlid)))
end))

let lresolve = (fun ( _67_123 ) ( x ) -> (match (_67_123) with
| LEnv (lenv) -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find lenv x.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(unbound_var x.Microsoft_FStar_Absyn_Syntax.idRange x)
end
| Some (x) -> begin
x
end)
end))

type tenv =
| TEnv of Microsoft_FStar_Backends_ML_Syntax.mlident Support.Microsoft.FStar.Util.smap

let is_TEnv = (fun ( _discr_ ) -> (match (_discr_) with
| TEnv (_) -> begin
true
end
| _ -> begin
false
end))

let tempty = (let _68_26396 = (Support.Microsoft.FStar.Util.smap_create 0)
in TEnv (_68_26396))

let tvsym = (fun ( _67_131 ) -> (match (_67_131) with
| (x, n) -> begin
(match ((Support.Microsoft.FStar.Util.starts_with x "\'")) with
| true -> begin
(x, n)
end
| false -> begin
((Support.String.strcat "\'" x), n)
end)
end))

let tenv_of_tvmap = (fun ( tvs ) -> (let rec fresh_tyvar = (fun ( used ) ( i ) -> (let pp = (tyvar_of_int 0)
in (match ((Support.Microsoft.FStar.Util.set_mem pp used)) with
| true -> begin
(fresh_tyvar used (i + 1))
end
| false -> begin
(let _68_26404 = (Support.Microsoft.FStar.Util.set_add pp used)
in (_68_26404, pp))
end)))
in (let freshen = (fun ( used ) ( pp ) -> (match (pp) with
| Some (pp) when (not ((Support.Microsoft.FStar.Util.set_mem pp.Microsoft_FStar_Absyn_Syntax.idText used))) -> begin
(let _68_26409 = (Support.Microsoft.FStar.Util.set_add pp.Microsoft_FStar_Absyn_Syntax.idText used)
in (_68_26409, pp.Microsoft_FStar_Absyn_Syntax.idText))
end
| _67_143 -> begin
(fresh_tyvar used 0)
end))
in (let _67_164 = (let for1 = (fun ( used ) ( tv ) -> (match (tv) with
| Some ((real, pp)) -> begin
(let _67_153 = (freshen used (Some (pp)))
in (match (_67_153) with
| (used, pp) -> begin
(let _68_26415 = (let _68_26414 = (fresh pp)
in (_68_26414, Some (real.Microsoft_FStar_Absyn_Syntax.idText)))
in (used, _68_26415))
end))
end
| None -> begin
(let _67_157 = (freshen used None)
in (match (_67_157) with
| (used, pp) -> begin
(let _68_26417 = (let _68_26416 = (fresh pp)
in (_68_26416, None))
in (used, _68_26417))
end))
end))
in (let _68_26421 = (Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> (match ((x = y)) with
| true -> begin
0
end
| false -> begin
1
end)) (fun ( x ) -> 0))
in (Support.Microsoft.FStar.Util.fold_map for1 _68_26421 tvs)))
in (match (_67_164) with
| (_67_162, tvs) -> begin
(let tparams = (Support.List.map (fun ( _67_168 ) -> (match (_67_168) with
| (x, _67_167) -> begin
(tvsym x)
end)) tvs)
in (let tvs = (Support.List.choose (fun ( _67_172 ) -> (match (_67_172) with
| (x, y) -> begin
(match (y) with
| None -> begin
None
end
| Some (y) -> begin
Some ((y, (tvsym x)))
end)
end)) tvs)
in (let _68_26425 = (let _68_26424 = (Support.Microsoft.FStar.Util.smap_of_list tvs)
in TEnv (_68_26424))
in (_68_26425, tparams))))
end)))))

let tvar_of_btvar = (fun ( _67_178 ) ( x ) -> (match (_67_178) with
| TEnv (tenv) -> begin
(let name = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
in (match ((Support.Microsoft.FStar.Util.smap_try_find tenv name)) with
| None -> begin
("", 0)
end
| Some (x) -> begin
(tvsym x)
end))
end))

let is_prim_ns = (fun ( ns ) -> (match (ns) with
| {Microsoft_FStar_Absyn_Syntax.idText = "Prims"; Microsoft_FStar_Absyn_Syntax.idRange = _67_186}::[] -> begin
true
end
| _67_191 -> begin
false
end))

type tprims =
| Tuple of int
| Exn

let is_Tuple = (fun ( _discr_ ) -> (match (_discr_) with
| Tuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exn = (fun ( _discr_ ) -> (match (_discr_) with
| Exn -> begin
true
end
| _ -> begin
false
end))

let as_tprims = (fun ( id ) -> (match ((is_prim_ns id.Microsoft_FStar_Absyn_Syntax.ns)) with
| true -> begin
(match (id.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText) with
| ("Tuple2") | ("DTuple2") -> begin
Some (Tuple (2))
end
| ("Tuple3") | ("DTuple3") -> begin
Some (Tuple (3))
end
| ("Tuple4") | ("DTuple4") -> begin
Some (Tuple (4))
end
| ("Tuple5") | ("DTuple5") -> begin
Some (Tuple (5))
end
| ("Tuple6") | ("DTuple6") -> begin
Some (Tuple (6))
end
| ("Tuple7") | ("DTuple7") -> begin
Some (Tuple (7))
end
| "exn" -> begin
Some (Exn)
end
| _67_209 -> begin
None
end)
end
| false -> begin
None
end))

let is_xtuple = (fun ( x ) -> (match ((is_prim_ns x.Microsoft_FStar_Absyn_Syntax.ns)) with
| true -> begin
(match (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText) with
| ("MkTuple2") | ("MkDTuple2") -> begin
Some (2)
end
| ("MkTuple3") | ("MkDTuple3") -> begin
Some (3)
end
| ("MkTuple4") | ("MkDTuple4") -> begin
Some (4)
end
| ("MkTuple5") | ("MkDTuple5") -> begin
Some (5)
end
| ("MkTuple6") | ("MkDTuple6") -> begin
Some (6)
end
| ("MkTuple7") | ("MkDTuple7") -> begin
Some (7)
end
| _67_224 -> begin
None
end)
end
| false -> begin
None
end))

let is_etuple = (fun ( e ) -> (match ((let _68_26446 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_26446.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _67_236)); Microsoft_FStar_Absyn_Syntax.tk = _67_233; Microsoft_FStar_Absyn_Syntax.pos = _67_231; Microsoft_FStar_Absyn_Syntax.fvs = _67_229; Microsoft_FStar_Absyn_Syntax.uvs = _67_227}, args)) -> begin
(let args = (Support.List.collect (fun ( _67_2 ) -> (match (_67_2) with
| (Support.Microsoft.FStar.Util.Inl (_67_245), _67_248) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _67_253) -> begin
(e)::[]
end)) args)
in (match ((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) when (k = (Support.List.length args)) -> begin
Some (k)
end
| _67_259 -> begin
None
end))
end
| _67_261 -> begin
None
end))

let is_ptuple = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, _67_265, args)) -> begin
(let args = (Support.Prims.pipe_right args (Support.List.collect (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end
| _67_277 -> begin
(p)::[]
end))))
in (match ((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
(match ((k = (Support.List.length args))) with
| true -> begin
Some (k)
end
| false -> begin
None
end)
end
| _67_282 -> begin
None
end))
end
| _67_284 -> begin
None
end))

let mlkind_of_kind = (fun ( tps ) ( k ) -> (let mltparam_of_tparam = (fun ( _67_3 ) -> (match (_67_3) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _67_297; Microsoft_FStar_Absyn_Syntax.pos = _67_295; Microsoft_FStar_Absyn_Syntax.fvs = _67_293; Microsoft_FStar_Absyn_Syntax.uvs = _67_291}; Microsoft_FStar_Absyn_Syntax.p = _67_289}), _67_304) -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.ppname))
end
| x -> begin
None
end))
in (let rec aux = (fun ( acc ) ( k ) -> (match ((let _68_26461 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _68_26461.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
Some ((Support.List.rev acc))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
Some ((Support.List.rev acc))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (([], k)) -> begin
(aux acc k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (x), _67_321)::rest, k2)) -> begin
(match ((aux [] x.Microsoft_FStar_Absyn_Syntax.sort)) with
| Some ([]) -> begin
(let x = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder (Support.Microsoft.FStar.Util.Inl (x), None))) with
| true -> begin
None
end
| false -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))
end)
in (let _68_26462 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (rest, k2) k.Microsoft_FStar_Absyn_Syntax.pos)
in (aux ((x)::acc) _68_26462)))
end
| _67_331 -> begin
None
end)
end
| _67_333 -> begin
None
end))
in (let aout = (Support.List.choose mltparam_of_tparam tps)
in (let some = (fun ( x ) -> Some (x))
in (let _68_26466 = (let _68_26465 = (Support.List.map some aout)
in (Support.List.rev _68_26465))
in (aux _68_26466 k)))))))

let rec mlty_of_ty_core = (fun ( mlenv ) ( tenv ) ( _67_341 ) -> (match (_67_341) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let ty = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (x) -> begin
(let _68_26482 = (tvar_of_btvar tenv x)
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (_68_26482))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _67_350; Microsoft_FStar_Absyn_Syntax.sort = ty; Microsoft_FStar_Absyn_Syntax.p = _67_347}, _67_353)) -> begin
(mlty_of_ty mlenv tenv (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _67_358)) -> begin
(mlty_of_ty mlenv tenv (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (([], c)) -> begin
(mlty_of_ty mlenv tenv (rg, (Microsoft_FStar_Absyn_Util.comp_result c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (((Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _67_367}), _67_373)::rest, c)) -> begin
(let t2 = (match (rest) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _67_381 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let mlt1 = (mlty_of_ty mlenv tenv (rg, t1))
in (let mlt2 = (mlty_of_ty mlenv tenv (rg, t2))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((mlt1, Microsoft_FStar_Backends_ML_Syntax.Keep, mlt2)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (((Support.Microsoft.FStar.Util.Inl (_67_387), _67_390)::rest, c)) -> begin
(let r = (match (rest) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _67_398 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlty_of_ty mlenv tenv (rg, r)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (_67_401) -> begin
(unexpected rg "type-constant")
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, [])) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t1, (Support.Microsoft.FStar.Util.Inl (t2), _67_412)::rest)) -> begin
(let t2 = (match (rest) with
| [] -> begin
t2
end
| _67_419 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t2, rest) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let mlt1 = (mlty_of_ty mlenv tenv (rg, t1))
in (let mlt2 = (mlty_of_ty mlenv tenv (rg, t2))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((mlt1, mlt2)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, (Support.Microsoft.FStar.Util.Inr (_67_426), _67_429)::rest)) -> begin
(let r = (match (rest) with
| [] -> begin
t
end
| _67_436 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, rest) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlty_of_ty mlenv tenv (rg, r)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_67_439) -> begin
(unsupported rg "type-fun")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_67_442) -> begin
(unexpected rg "type-meta")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_67_445) -> begin
(unexpected rg "type-uvar")
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(unexpected rg "type-unknown")
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_67_449) -> begin
(unexpected rg "type-delayed")
end)))
end))
and maybe_named = (fun ( mlenv ) ( tenv ) ( _67_455 ) -> (match (_67_455) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec aux = (fun ( acc ) ( _67_461 ) -> (match (_67_461) with
| (rg, ty) -> begin
(match ((let _68_26493 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _68_26493.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(let _68_26495 = (let _68_26494 = (mlpath_of_lident mlenv c.Microsoft_FStar_Absyn_Syntax.v)
in (_68_26494, acc))
in Some (_68_26495))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(match ((Support.Prims.pipe_right args (Support.Microsoft.FStar.Util.for_some (fun ( _67_4 ) -> (match (_67_4) with
| (Support.Microsoft.FStar.Util.Inr (_67_470), _67_473) -> begin
true
end
| _67_476 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let tys = (Support.Prims.pipe_right args (Support.List.map (fun ( _67_5 ) -> (match (_67_5) with
| (Support.Microsoft.FStar.Util.Inl (t), _67_481) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| _67_484 -> begin
(failwith ("impos"))
end))))
in (aux (Support.List.append tys acc) (rg, head)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _67_490; Microsoft_FStar_Absyn_Syntax.sort = ty; Microsoft_FStar_Absyn_Syntax.p = _67_487}, _67_493)) -> begin
(aux acc (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _67_498)) -> begin
(aux acc (rg, ty))
end
| _67_502 -> begin
None
end)
end))
in (aux [] (rg, ty))))
end))
and maybe_tuple = (fun ( mlenv ) ( tenv ) ( _67_507 ) -> (match (_67_507) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec unfun = (fun ( n ) ( ty ) -> (match ((n <= 0)) with
| true -> begin
Some (ty)
end
| false -> begin
(match ((let _68_26505 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _68_26505.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, ty)) -> begin
(unfun (n - (Support.List.length bs)) ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _67_518)) -> begin
(unfun n ty)
end
| _67_522 -> begin
None
end)
end))
in (let rec aux = (fun ( acc ) ( ty ) -> (match ((let _68_26510 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _68_26510.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(match ((as_tprims c.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (Tuple (n)) -> begin
(match (((Support.List.length acc) <> n)) with
| true -> begin
None
end
| false -> begin
(let _68_26512 = (Support.List.map (fun ( ty ) -> (mlty_of_ty mlenv tenv (rg, ty))) acc)
in Some (_68_26512))
end)
end
| _67_533 -> begin
None
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(match ((Support.Prims.pipe_right args (Support.Microsoft.FStar.Util.for_some (fun ( _67_6 ) -> (match (_67_6) with
| (Support.Microsoft.FStar.Util.Inr (_67_540), _67_543) -> begin
true
end
| (Support.Microsoft.FStar.Util.Inl (t), _67_548) -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let tys = (Support.Prims.pipe_right args (Support.List.map (fun ( _67_7 ) -> (match (_67_7) with
| (Support.Microsoft.FStar.Util.Inl (t), _67_554) -> begin
t
end
| _67_557 -> begin
(failwith ("impos"))
end))))
in (aux (Support.List.append tys acc) head))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _67_561)) -> begin
(aux acc ty)
end
| _67_565 -> begin
None
end))
in (aux [] ty))))
end))
and mlty_of_ty = (fun ( mlenv ) ( tenv ) ( rgty ) -> (match ((maybe_tuple mlenv tenv rgty)) with
| Some (x) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (x)
end
| None -> begin
(match ((maybe_named mlenv tenv rgty)) with
| Some (x) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (((Support.Prims.snd x), (Support.Prims.fst x)))
end
| None -> begin
(mlty_of_ty_core mlenv tenv rgty)
end)
end))

let mltycons_of_mlty = (fun ( ty ) -> (let rec aux = (fun ( acc ) ( ty ) -> (match (ty) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((dom, _67_581, codom)) -> begin
(aux ((dom)::acc) codom)
end
| _67_586 -> begin
((Support.List.rev acc), ty)
end))
in (aux [] ty)))

let rec strip_polymorphism = (fun ( acc ) ( rg ) ( ty ) -> (let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (match ((let _68_26527 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _68_26527.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _67_618 = (Support.Prims.pipe_right bs (Support.List.partition (fun ( _67_8 ) -> (match (_67_8) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _67_605; Microsoft_FStar_Absyn_Syntax.pos = _67_603; Microsoft_FStar_Absyn_Syntax.fvs = _67_601; Microsoft_FStar_Absyn_Syntax.uvs = _67_599}; Microsoft_FStar_Absyn_Syntax.p = _67_597}), _67_612) -> begin
true
end
| _67_615 -> begin
false
end))))
in (match (_67_618) with
| (ts, vs) -> begin
(let ts = (Support.Prims.pipe_right ts (Support.List.collect (fun ( _67_9 ) -> (match (_67_9) with
| (Support.Microsoft.FStar.Util.Inl (x), _67_623) -> begin
((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))::[]
end
| _67_626 -> begin
[]
end))))
in (match ((vs, c.Microsoft_FStar_Absyn_Syntax.n)) with
| ([], Microsoft_FStar_Absyn_Syntax.Total (ty)) -> begin
(ts, rg, ty)
end
| ([], Microsoft_FStar_Absyn_Syntax.Comp (c)) -> begin
(ts, rg, c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| (_67_637, _67_639) -> begin
(let _68_26530 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (vs, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
in (ts, rg, _68_26530))
end))
end))
end
| _67_642 -> begin
((Support.List.rev acc), rg, ty)
end)))

let mlscheme_of_ty = (fun ( mlenv ) ( rg ) ( ty ) -> (let _67_649 = (strip_polymorphism [] rg ty)
in (match (_67_649) with
| (tparams, rg, ty) -> begin
(let some = (fun ( x ) -> Some (x))
in (let _67_654 = (let _68_26539 = (Support.List.map some tparams)
in (tenv_of_tvmap _68_26539))
in (match (_67_654) with
| (tenv, tparams) -> begin
(let _68_26540 = (mlty_of_ty mlenv tenv (rg, ty))
in (tparams, _68_26540))
end)))
end)))

let mlconst_of_const = (fun ( sctt ) -> (match (sctt) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Unit
end
| Microsoft_FStar_Absyn_Syntax.Const_char (c) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Char (c)
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (c) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Byte (c)
end
| Microsoft_FStar_Absyn_Syntax.Const_int (c) -> begin
(let _68_26544 = (let _68_26543 = (Support.Microsoft.FStar.Util.int_of_string c)
in (Support.Microsoft.FStar.Util.int32_of_int _68_26543))
in Microsoft_FStar_Backends_ML_Syntax.MLC_Int32 (_68_26544))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Int32 (i)
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (i) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Int64 (i)
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (b)
end
| Microsoft_FStar_Absyn_Syntax.Const_float (d) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Float (d)
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((bytes, _67_673)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Bytes (bytes)
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _67_678)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_String ((Support.Microsoft.FStar.Util.string_of_unicode bytes))
end))

let rec mlpat_of_pat = (fun ( mlenv ) ( rg ) ( le ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, _67_687, ps)) -> begin
(let ps = (Support.Prims.pipe_right ps (Support.List.filter (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
false
end
| _67_699 -> begin
true
end))))
in (match (((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v) = Some ((Support.List.length ps)))) with
| true -> begin
(let _67_705 = (Support.Microsoft.FStar.Util.fold_map (fun ( le ) ( pat ) -> (mlpat_of_pat mlenv pat.Microsoft_FStar_Absyn_Syntax.p le pat)) le ps)
in (match (_67_705) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps))
end))
end
| false -> begin
(let _67_708 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_67_708) with
| (le, ps) -> begin
(let p = (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
(let _68_26560 = (let _68_26559 = (path_of_ns mlenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (let _68_26558 = (let _68_26557 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.List.zip _68_26557 ps))
in (_68_26559, _68_26558)))
in Microsoft_FStar_Backends_ML_Syntax.MLP_Record (_68_26560))
end
| None -> begin
(let _68_26562 = (let _68_26561 = (mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v)
in (_68_26561, ps))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_68_26562))
end)
in (le, p))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _67_716)) -> begin
(let _67_721 = (lpush le x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_67_721) with
| (le, mlid) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Var (mlid))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _68_26564 = (let _68_26563 = (mlconst_of_const c)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Const (_68_26563))
in (le, _68_26564))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _67_728 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_67_728) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_67_730) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_67_733) -> begin
(unsupported rg "top-level-dot-patterns")
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_67_736) -> begin
(unsupported rg "top-level-dot-patterns")
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (_67_739) -> begin
(unsupported rg "pattern-type-variable")
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_67_742) -> begin
(unsupported rg "pattern-type-wild")
end))

let rec mlexpr_of_expr = (fun ( mlenv ) ( rg ) ( lenv ) ( e ) -> (let rg = e.Microsoft_FStar_Absyn_Syntax.pos
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let rec eta_expand_dataconst = (fun ( ct ) ( args ) ( nvars ) -> (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let rec bvs = (fun ( _67_10 ) -> (match (_67_10) with
| 0 -> begin
[]
end
| n -> begin
(let _67_759 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _68_26595 = (let _68_26593 = (let _68_26592 = (let _68_26590 = (let _68_26589 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _68_26589))
in (Support.String.strcat "__dataconst_" _68_26590))
in (let _68_26591 = (Support.ST.read ctr)
in (_68_26592, _68_26591)))
in (_68_26593, None))
in (let _68_26594 = (bvs (n - 1))
in (_68_26595)::_68_26594)))
end))
in (let vs = (bvs nvars)
in (let fapp = (let _68_26599 = (let _68_26598 = (let _68_26597 = (Support.List.map (fun ( _67_765 ) -> (match (_67_765) with
| (x, _67_764) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Var (x)
end)) vs)
in (Support.List.append args _68_26597))
in (ct, _68_26598))
in Microsoft_FStar_Backends_ML_Syntax.MLE_CTor (_68_26599))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((vs, fapp)))))))
in (let mkCTor = (fun ( c ) ( args ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
(let _68_26608 = (let _68_26607 = (path_of_ns mlenv c.Microsoft_FStar_Absyn_Syntax.ns)
in (let _68_26606 = (let _68_26605 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.List.zip _68_26605 args))
in (_68_26607, _68_26606)))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Record (_68_26608))
end
| None -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((n, _67_776)) when (n > (Support.List.length args)) -> begin
(let _68_26609 = (mlpath_of_lident mlenv c)
in (eta_expand_dataconst _68_26609 args (n - (Support.List.length args))))
end
| _67_780 -> begin
(let _68_26611 = (let _68_26610 = (mlpath_of_lident mlenv c)
in (_68_26610, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_CTor (_68_26611))
end)
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((sube, args)) -> begin
(match ((sube.Microsoft_FStar_Absyn_Syntax.n, args)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _67_798::_67_796::(Support.Microsoft.FStar.Util.Inr (a1), _67_793)::a2::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_left") -> begin
(mlexpr_of_expr mlenv rg lenv (let _67_801 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a1, (a2)::[])); Microsoft_FStar_Absyn_Syntax.tk = _67_801.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _67_801.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _67_801.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _67_801.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _67_816::_67_814::a1::(Support.Microsoft.FStar.Util.Inr (a2), _67_810)::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_right") -> begin
(mlexpr_of_expr mlenv rg lenv (let _67_819 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a2, (a1)::[])); Microsoft_FStar_Absyn_Syntax.tk = _67_819.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _67_819.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _67_819.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _67_819.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _67_826) when ((((c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assume") || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assert")) || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.erase")) || (Support.Microsoft.FStar.Util.starts_with c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText "l__")) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Unit)
end
| (_67_829, _67_831) -> begin
(match ((is_etuple e)) with
| Some (k) -> begin
(let args = (Support.List.collect (fun ( _67_11 ) -> (match (_67_11) with
| (Support.Microsoft.FStar.Util.Inl (_67_837), _67_840) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _67_845) -> begin
(let _68_26613 = (mlexpr_of_expr mlenv rg lenv e)
in (_68_26613)::[])
end)) args)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (args))
end
| _67_849 -> begin
(let args = (Support.List.collect (fun ( _67_12 ) -> (match (_67_12) with
| (Support.Microsoft.FStar.Util.Inl (_67_852), _67_855) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _67_860) -> begin
(let _68_26615 = (mlexpr_of_expr mlenv rg lenv e)
in (_68_26615)::[])
end)) args)
in (match (sube) with
| ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) | ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)
end
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, _67_902)); Microsoft_FStar_Absyn_Syntax.tk = _67_899; Microsoft_FStar_Absyn_Syntax.pos = _67_897; Microsoft_FStar_Absyn_Syntax.fvs = _67_895; Microsoft_FStar_Absyn_Syntax.uvs = _67_893} -> begin
(let subns = (let _68_26617 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (Support.String.concat "." _68_26617))
in (let _67_914 = (match ((Support.List.rev c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)) with
| [] -> begin
("", [])
end
| h::t -> begin
(h.Microsoft_FStar_Absyn_Syntax.idText, (Support.List.rev t))
end)
in (match (_67_914) with
| (rn, subnsl) -> begin
(match ((let _68_26618 = (Support.Microsoft.FStar.Util.smap_try_find record_constructors subns)
in (_68_26618, args))) with
| (Some (_67_916), arg::[]) -> begin
(let _68_26621 = (let _68_26620 = (let _68_26619 = (path_of_ns mlenv subnsl)
in (_68_26619, c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (arg, _68_26620))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Proj (_68_26621))
end
| (Some (_67_922), arg::args) -> begin
(let _68_26626 = (let _68_26625 = (let _68_26624 = (let _68_26623 = (let _68_26622 = (path_of_ns mlenv subnsl)
in (_68_26622, c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (arg, _68_26623))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Proj (_68_26624))
in (_68_26625, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_68_26626))
end
| _67_929 -> begin
(let _68_26628 = (let _68_26627 = (mlexpr_of_expr mlenv rg lenv sube)
in (_68_26627, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_68_26628))
end)
end)))
end
| _67_931 -> begin
(let _68_26630 = (let _68_26629 = (mlexpr_of_expr mlenv rg lenv sube)
in (_68_26629, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_68_26630))
end))
end)
end)
end
| _67_933 -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _68_26631 = (lresolve lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Var (_68_26631))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) -> begin
(mkCTor x.Microsoft_FStar_Absyn_Syntax.v [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _67_943)) -> begin
(let fid = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (match ((((Support.Microsoft.FStar.Util.starts_with fid "is_") && ((Support.String.length fid) > 3)) && (let _68_26632 = (Support.Microsoft.FStar.Util.char_at fid 3)
in (Support.Microsoft.FStar.Util.is_upper _68_26632)))) with
| true -> begin
(let sub = (Support.Microsoft.FStar.Util.substring_from fid 3)
in (let mlid = (fresh "_discr_")
in (let rid = (let _67_949 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ns = _67_949.Microsoft_FStar_Absyn_Syntax.ns; Microsoft_FStar_Absyn_Syntax.ident = (let _67_951 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = sub; Microsoft_FStar_Absyn_Syntax.idRange = _67_951.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = _67_949.Microsoft_FStar_Absyn_Syntax.nsstr; Microsoft_FStar_Absyn_Syntax.str = sub})
in (let _68_26640 = (let _68_26639 = (let _68_26638 = (let _68_26637 = (let _68_26636 = (let _68_26635 = (let _68_26634 = (let _68_26633 = (mlpath_of_lident mlenv rid)
in (_68_26633, (Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)::[]))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_68_26634))
in (_68_26635, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (true))))
in (_68_26636)::((Microsoft_FStar_Backends_ML_Syntax.MLP_Wild, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (false))))::[])
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_ML_Syntax.idsym mlid))), _68_26637))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match (_68_26638))
in (((mlid, None))::[], _68_26639))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun (_68_26640)))))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr)) with
| Some ((_67_955, projs)) -> begin
(let mlid = (fresh "_proj_")
in (let cargs = (Support.List.map (fun ( x ) -> (let _68_26642 = (fresh x)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Var (_68_26642))) projs)
in (let _67_964 = (Support.List.rev x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_67_964) with
| cn::cr -> begin
(let crstr = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) cr)
in (let rid = {Microsoft_FStar_Absyn_Syntax.ns = cr; Microsoft_FStar_Absyn_Syntax.ident = (let _67_967 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = cn.Microsoft_FStar_Absyn_Syntax.idText; Microsoft_FStar_Absyn_Syntax.idRange = _67_967.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = (Support.String.concat "." crstr); Microsoft_FStar_Absyn_Syntax.str = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr}
in (let cn = cn.Microsoft_FStar_Absyn_Syntax.idText
in (let _68_26651 = (let _68_26650 = (let _68_26649 = (let _68_26648 = (let _68_26647 = (let _68_26646 = (let _68_26645 = (let _68_26644 = (mlpath_of_lident mlenv rid)
in (_68_26644, cargs))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_68_26645))
in (_68_26646, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))))
in (_68_26647)::[])
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_ML_Syntax.idsym mlid))), _68_26648))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match (_68_26649))
in (((mlid, None))::[], _68_26650))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun (_68_26651)))))
end))))
end
| None -> begin
(let _68_26652 = (mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Name (_68_26652))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _68_26653 = (mlconst_of_const c)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Const (_68_26653))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (([], e)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inl (_67_980), _67_983)::rest, e)) -> begin
(let _68_26654 = (match ((Support.List.isEmpty rest)) with
| true -> begin
e
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlexpr_of_expr mlenv rg lenv _68_26654))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inr (x), _67_993)::rest, e)) -> begin
(let _67_1001 = (lpush lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_67_1001) with
| (lenv, mlid) -> begin
(let e = (let _68_26655 = (match ((Support.List.isEmpty rest)) with
| true -> begin
e
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlexpr_of_expr mlenv rg lenv _68_26655))
in (Microsoft_FStar_Backends_ML_Syntax.mlfun mlid e))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((x, (p, None, e)::[])) when (Microsoft_FStar_Absyn_Util.is_wild_pat p) -> begin
(match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_67_1012) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_67_1015) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| _67_1018 -> begin
(failwith ("Impossible"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, bs)) -> begin
(match (bs) with
| (({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e1)::({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e2)::[]) | (({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e1)::({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e2)::[]) -> begin
(let e = (mlexpr_of_expr mlenv rg lenv e)
in (let e1 = (mlexpr_of_expr mlenv rg lenv e1)
in (let e2 = (mlexpr_of_expr mlenv rg lenv e2)
in (Microsoft_FStar_Backends_ML_Syntax.mlif e (e1, e2)))))
end
| _67_1071 -> begin
(let e = (mlexpr_of_expr mlenv rg lenv e)
in (let bs = (Support.List.map (mlbranch_of_branch mlenv rg lenv) bs)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((e, bs))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((rec_, lb), body)) -> begin
(let _67_1082 = (mllets_of_lets mlenv rg lenv (rec_, lb))
in (match (_67_1082) with
| (lenv, bindings) -> begin
(let body = (mlexpr_of_expr mlenv rg lenv body)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, bindings), body)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let _67_1089 = ()
in (let _67_1129 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) | (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) -> begin
(c, args)
end
| _67_1126 -> begin
(unexpected rg "meta-data-app-without-fvar")
end)
in (match (_67_1129) with
| (c, args) -> begin
(let args = (Support.Prims.pipe_right args (Support.List.collect (fun ( _67_13 ) -> (match (_67_13) with
| (Support.Microsoft.FStar.Util.Inr (e), _67_1134) -> begin
(e)::[]
end
| _67_1137 -> begin
[]
end))))
in (let args = (Support.List.map (mlexpr_of_expr mlenv rg lenv) args)
in (mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_67_1152); Microsoft_FStar_Absyn_Syntax.lbtyp = _67_1150; Microsoft_FStar_Absyn_Syntax.lbeff = _67_1148; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let d1 = (mlexpr_of_expr mlenv rg lenv e1)
in (let d2 = (mlexpr_of_expr mlenv rg lenv e2)
in (Microsoft_FStar_Backends_ML_Syntax.mlseq d1 d2)))
end
| _67_1163 -> begin
(unexpected rg "expr-seq-mark-without-let")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Primop))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _67_1171, _67_1173)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.MaskedEffect))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_67_1182) -> begin
(unexpected rg "expr-app")
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_67_1185) -> begin
(unexpected rg "expr-uvar")
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_67_1188) -> begin
(unexpected rg "expr-delayed")
end)
end))))))
and mllets_of_lets = (fun ( mlenv ) ( rg ) ( lenv ) ( _67_1195 ) -> (match (_67_1195) with
| (rec_, lbs) -> begin
(let downct = (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(x, lb.Microsoft_FStar_Absyn_Syntax.lbdef)
end
| Support.Microsoft.FStar.Util.Inr (_67_1201) -> begin
(unexpected rg "expr-let-in-with-fvar")
end))
in (let lbs = (Support.List.map downct lbs)
in (let _67_1211 = (Support.Microsoft.FStar.Util.fold_map (fun ( lenv ) ( _67_1208 ) -> (match (_67_1208) with
| (x, _67_1207) -> begin
(lpush lenv x.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.ppname)
end)) lenv lbs)
in (match (_67_1211) with
| (lenvb, mlids) -> begin
(let es = (let inlenv = (match (rec_) with
| true -> begin
lenvb
end
| false -> begin
lenv
end)
in (Support.List.map (fun ( _67_1215 ) -> (match (_67_1215) with
| (x, e) -> begin
(let mlid = (lresolve lenvb x.Microsoft_FStar_Absyn_Syntax.realname)
in (let _68_26666 = (mlexpr_of_expr mlenv rg inlenv e)
in (mlid, None, [], _68_26666)))
end)) lbs))
in (lenvb, es))
end))))
end))
and mlbranch_of_branch = (fun ( mlenv ) ( rg ) ( lenv ) ( _67_1224 ) -> (match (_67_1224) with
| (pat, when_, body) -> begin
(let _67_1227 = (mlpat_of_pat mlenv rg lenv pat)
in (match (_67_1227) with
| (lenv, pat) -> begin
(let when_ = (Support.Option.map (mlexpr_of_expr mlenv rg lenv) when_)
in (let body = (mlexpr_of_expr mlenv rg lenv body)
in (pat, when_, body)))
end))
end))

type mode =
| Sig
| Struct

let is_Sig = (fun ( _discr_ ) -> (match (_discr_) with
| Sig -> begin
true
end
| _ -> begin
false
end))

let is_Struct = (fun ( _discr_ ) -> (match (_discr_) with
| Struct -> begin
true
end
| _ -> begin
false
end))

type mlitem1 =
(Microsoft_FStar_Backends_ML_Syntax.mlsig1, Microsoft_FStar_Backends_ML_Syntax.mlmodule1) Support.Microsoft.FStar.Util.either

let mlitem1_ty = (fun ( mode ) ( args ) -> (match (mode) with
| Sig -> begin
Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (args))
end
| Struct -> begin
Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (args))
end))

let mlitem1_exn = (fun ( mode ) ( args ) -> (match (mode) with
| Sig -> begin
Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_ML_Syntax.MLS_Exn (args))
end
| Struct -> begin
Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_ML_Syntax.MLM_Exn (args))
end))

type mldtype =
(Microsoft_FStar_Backends_ML_Syntax.mlsymbol * Microsoft_FStar_Backends_ML_Syntax.mlidents * Microsoft_FStar_Backends_ML_Syntax.mltybody)

type fstypes =
| DT of (string * Microsoft_FStar_Absyn_Syntax.lident list * Microsoft_FStar_Backends_ML_Syntax.mlident list * Support.Microsoft.FStar.Range.range)
| Rec of (string * Microsoft_FStar_Absyn_Syntax.ident list * Microsoft_FStar_Absyn_Syntax.lident list * Microsoft_FStar_Backends_ML_Syntax.mlident list * Support.Microsoft.FStar.Range.range)
| Abb of (string * Microsoft_FStar_Absyn_Syntax.typ * (tenv * Microsoft_FStar_Backends_ML_Syntax.mlident list) * Support.Microsoft.FStar.Range.range)

let is_DT = (fun ( _discr_ ) -> (match (_discr_) with
| DT (_) -> begin
true
end
| _ -> begin
false
end))

let is_Rec = (fun ( _discr_ ) -> (match (_discr_) with
| Rec (_) -> begin
true
end
| _ -> begin
false
end))

let is_Abb = (fun ( _discr_ ) -> (match (_discr_) with
| Abb (_) -> begin
true
end
| _ -> begin
false
end))

let mldtype_of_indt = (fun ( mlenv ) ( indt ) -> (let rec getRecordFieldsFromType = (fun ( _67_14 ) -> (match (_67_14) with
| [] -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.RecordType (f)::_67_1250 -> begin
(let _68_26709 = (Support.Prims.pipe_right f (Support.List.map (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.ident)))
in Some (_68_26709))
end
| _67_1257::qualif -> begin
(getRecordFieldsFromType qualif)
end))
in (let rec comp_vars = (fun ( ct ) -> (match (ct) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(type_vars t.Microsoft_FStar_Absyn_Syntax.n)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(type_vars ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.n)
end))
and type_vars = (fun ( ty ) -> (match (ty) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _68_26716 = (Support.Prims.pipe_right bs (Support.List.collect (fun ( _67_15 ) -> (match (_67_15) with
| (Support.Microsoft.FStar.Util.Inr (x), _67_1275) -> begin
(let tl = (type_vars x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n)
in (let hd = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder (Support.Microsoft.FStar.Util.Inr (x), None))) with
| true -> begin
None
end
| false -> begin
Some (x.Microsoft_FStar_Absyn_Syntax.v)
end)
in (hd)::[]))
end
| _67_1280 -> begin
[]
end))))
in (let _68_26715 = (comp_vars c.Microsoft_FStar_Absyn_Syntax.n)
in (Support.List.append _68_26716 _68_26715)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t))) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) -> begin
(type_vars t.Microsoft_FStar_Absyn_Syntax.n)
end
| _67_1314 -> begin
[]
end))
in (let _67_1388 = (let fold1 = (fun ( sigelt ) ( _67_1319 ) -> (match (_67_1319) with
| (types, ctors) -> begin
(match (sigelt) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((x, tps, k, ts, cs, qualif, rg)) -> begin
(match ((Support.List.contains Microsoft_FStar_Absyn_Syntax.Logic qualif)) with
| true -> begin
(types, ctors)
end
| false -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let ty = (match ((let _68_26721 = (getRecordFieldsFromType qualif)
in (_68_26721, cs))) with
| (Some (f), c::[]) -> begin
(let _67_1338 = (Support.Microsoft.FStar.Util.smap_add record_constructors c.Microsoft_FStar_Absyn_Syntax.str f)
in (let _68_26724 = (let _68_26723 = (let _68_26722 = (tenv_of_tvmap ar)
in (Support.Prims.snd _68_26722))
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, f, cs, _68_26723, rg))
in Rec (_68_26724)))
end
| (_67_1341, _67_1343) -> begin
(let _68_26727 = (let _68_26726 = (let _68_26725 = (tenv_of_tvmap ar)
in (Support.Prims.snd _68_26725))
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, cs, _68_26726, rg))
in DT (_68_26727))
end)
in ((ty)::types, ctors)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, pr, _67_1350, _67_1352, rg)) -> begin
(let actr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let anames = (let _68_26731 = (type_vars ty.Microsoft_FStar_Absyn_Syntax.n)
in (Support.List.map (fun ( _67_16 ) -> (match (_67_16) with
| None -> begin
(let _67_1359 = (Support.Microsoft.FStar.Util.incr actr)
in (let _68_26730 = (let _68_26729 = (Support.ST.read actr)
in (Support.Microsoft.FStar.Util.string_of_int _68_26729))
in (Support.String.strcat "_" _68_26730)))
end
| Some (x) -> begin
(let _67_1363 = (Support.Microsoft.FStar.Util.incr actr)
in x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end)) _68_26731))
in (let _67_1366 = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.str ((Support.List.length anames), anames))
in (types, ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (ty, pr)))::ctors))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((x, tps, k, body, _67_1373, rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _68_26735 = (let _68_26734 = (let _68_26733 = (let _68_26732 = (tenv_of_tvmap ar)
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, body, _68_26732, rg))
in Abb (_68_26733))
in (_68_26734)::types)
in (_68_26735, ctors)))
end
| _67_1382 -> begin
(unexpected (Microsoft_FStar_Absyn_Util.range_of_sigelt sigelt) "no-dtype-or-abbrvs-in-bundle")
end)
end))
in (let _67_1385 = (Support.List.fold_right fold1 indt ([], []))
in (match (_67_1385) with
| (ts, cs) -> begin
(let _68_26736 = (Support.Microsoft.FStar.Util.smap_of_list cs)
in (ts, _68_26736))
end)))
in (match (_67_1388) with
| (ts, cs) -> begin
(let cons_args = (fun ( cname ) ( tparams ) ( rg ) ( x ) -> (let _67_1397 = (let _68_26745 = (Support.Microsoft.FStar.Util.smap_try_find cs cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.Prims.pipe_right _68_26745 Support.Microsoft.FStar.Util.must))
in (match (_67_1397) with
| (c, _67_1396) -> begin
(let _67_1401 = (strip_polymorphism [] rg c)
in (match (_67_1401) with
| (cparams, rgty, c) -> begin
(let _67_1402 = (match (((Support.List.length cparams) <> (Support.List.length tparams))) with
| true -> begin
(unexpected rg "invalid-number-of-ctor-params")
end
| false -> begin
()
end)
in (let cparams = (Support.List.map (fun ( _67_1407 ) -> (match (_67_1407) with
| (x, _67_1406) -> begin
x.Microsoft_FStar_Absyn_Syntax.idText
end)) cparams)
in (let tenv = (Support.List.zip cparams tparams)
in (let tenv = (let _68_26747 = (Support.Microsoft.FStar.Util.smap_of_list tenv)
in TEnv (_68_26747))
in (let c = (mlty_of_ty mlenv tenv (rgty, c))
in (let _67_1414 = (mltycons_of_mlty c)
in (match (_67_1414) with
| (args, name) -> begin
(match (name) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((tyargs, name)) when ((Support.Prims.snd name) = x) -> begin
(let check = (fun ( x ) ( mty ) -> (match (mty) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (mtyx) -> begin
(x = mtyx)
end
| _67_1425 -> begin
false
end))
in (let _67_1426 = (match (((Support.List.length tyargs) <> (Support.List.length cparams))) with
| true -> begin
(unexpected rg "dtype-invalid-ctor-result")
end
| false -> begin
()
end)
in (let _67_1428 = (match ((not ((Support.List.forall2 check tparams tyargs)))) with
| true -> begin
(unsupported rg "dtype-invalid-ctor-result")
end
| false -> begin
()
end)
in args)))
end
| _67_1431 -> begin
(unexpected rg "dtype-invalid-ctor-result")
end)
end)))))))
end))
end)))
in (let fortype = (fun ( ty ) -> (match (ty) with
| DT ((x, tcs, tparams, rg)) -> begin
(let mldcons_of_cons = (fun ( cname ) -> (let args = (cons_args cname tparams rg x)
in (cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))
in (let _68_26757 = (let _68_26756 = (Support.List.map mldcons_of_cons tcs)
in Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (_68_26756))
in (x, tparams, _68_26757)))
end
| Rec ((x, f, tcs, tparams, rg)) -> begin
(let args = (match (tcs) with
| cname::[] -> begin
(cons_args cname tparams rg x)
end
| _67_1453 -> begin
(unexpected rg "records-should-have-one-single-constructor")
end)
in (let mldproj_of_proj = (fun ( name ) ( c ) -> (name.Microsoft_FStar_Absyn_Syntax.idText, c))
in (let _67_1459 = (match (((Support.List.length f) <> (Support.List.length args))) with
| true -> begin
(let _68_26768 = (let _68_26767 = (let _68_26762 = (Support.List.hd tcs)
in _68_26762.Microsoft_FStar_Absyn_Syntax.str)
in (let _68_26766 = (let _68_26764 = (Support.List.map (fun ( f ) -> f.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.Prims.pipe_right _68_26764 (Support.String.concat ", ")))
in (let _68_26765 = (Support.Prims.pipe_right (Support.List.length args) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format4 "%s, %s, %s fields, %s args" x _68_26767 _68_26766 _68_26765))))
in (unexpected rg _68_26768))
end
| false -> begin
()
end)
in (let _68_26770 = (let _68_26769 = (Support.List.map2 mldproj_of_proj f args)
in Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (_68_26769))
in (x, tparams, _68_26770)))))
end
| Abb ((x, body, (tenv, tparams), rg)) -> begin
(let body = (mlty_of_ty mlenv tenv (rg, body))
in (x, tparams, Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (body)))
end))
in (Support.List.map fortype ts)))
end)))))

let mlmod1_of_mod1 = (fun ( mode ) ( mlenv ) ( modx ) -> (let export_val = (fun ( qal ) -> (let export_val1 = (fun ( _67_17 ) -> (match (_67_17) with
| (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) | (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Private) -> begin
false
end
| _67_1485 -> begin
true
end))
in (Support.List.for_all export_val1 qal)))
in (match (modx) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_67_1488) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when ((export_val qal) && (mode = Sig)) -> begin
(let _67_1498 = (mlscheme_of_ty mlenv rg ty)
in (match (_67_1498) with
| (tparams, ty) -> begin
Some (Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (tparams, ty)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when (mode = Sig) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((rec_, lbs), rg, _67_1510, _67_1512)) when (mode = Struct) -> begin
(let downct = (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(x, lb.Microsoft_FStar_Absyn_Syntax.lbdef)
end
| Support.Microsoft.FStar.Util.Inl (_67_1520) -> begin
(unexpected rg "expr-top-let-with-bvar")
end))
in (let lbs = (Support.List.map downct lbs)
in (let lbs = (Support.List.map (fun ( _67_1525 ) -> (match (_67_1525) with
| (x, e) -> begin
(let _68_26784 = (mlexpr_of_expr mlenv rg (lenv_of_mlenv mlenv) e)
in ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (- (1))), None, [], _68_26784))
end)) lbs)
in Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lbs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, rg)) when (mode = Struct) -> begin
(let lenv = (lenv_of_mlenv mlenv)
in (let _68_26787 = (let _68_26786 = (let _68_26785 = (mlexpr_of_expr mlenv rg lenv e)
in Microsoft_FStar_Backends_ML_Syntax.MLM_Top (_68_26785))
in Support.Microsoft.FStar.Util.Inr (_68_26786))
in Some (_68_26787)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_67_1533, _67_1535, _67_1537, _67_1539, qal, _67_1542)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((t, tps, k, ty, _67_1550, rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _67_1560 = (tenv_of_tvmap ar)
in (match (_67_1560) with
| (tenv, tparams) -> begin
(let ty = (mlty_of_ty mlenv tenv (rg, ty))
in (let ty = Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (ty)
in Some ((mlitem1_ty mode (((t.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, tparams, Some (ty)))::[])))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, [], [], [], rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _67_1578 = (tenv_of_tvmap ar)
in (match (_67_1578) with
| (_tenv, tparams) -> begin
Some ((mlitem1_ty mode (((t.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, tparams, None))::[])))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_67_1592, _67_1594, _67_1596, qal, _67_1599, _67_1601))::[], _67_1606, _67_1608, _67_1610)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, (tx, _67_1617, _67_1619), qal, _67_1623, rg))::[], _67_1629, _67_1631, _67_1633)) when ((as_tprims tx) = Some (Exn)) -> begin
(let rec aux = (fun ( acc ) ( ty ) -> (match ((let _68_26792 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _68_26792.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let tys = (Support.Prims.pipe_right bs (Support.List.collect (fun ( _67_18 ) -> (match (_67_18) with
| (Support.Microsoft.FStar.Util.Inl (_67_1645), _67_1648) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _67_1653) -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort)::[]
end))))
in tys)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (x) when ((as_tprims x.Microsoft_FStar_Absyn_Syntax.v) = Some (Exn)) -> begin
(Support.List.rev acc)
end
| _67_1659 -> begin
(unexpected rg "invalid-exn-type")
end))
in (let args = (aux [] ty)
in (let tenv = (let _68_26794 = (tenv_of_tvmap [])
in (Support.Prims.fst _68_26794))
in (let args = (Support.List.map (fun ( ty ) -> (mlty_of_ty mlenv tenv (rg, ty))) args)
in Some ((mlitem1_exn mode (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((indt, _67_1666, _67_1668, _67_1670)) -> begin
(let aout = (mldtype_of_indt mlenv indt)
in (let aout = (Support.List.map (fun ( _67_1677 ) -> (match (_67_1677) with
| (x, y, z) -> begin
(x, y, Some (z))
end)) aout)
in (match (mode) with
| Sig -> begin
Some (Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (aout)))
end
| Struct -> begin
Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (aout)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume (_67_1682) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_67_1685) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_67_1688) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_67_1691) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_67_1694) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (_67_1697) -> begin
None
end)))

let mlmod_of_mod = (fun ( mlenv ) ( modx ) -> (let asright = (fun ( _67_19 ) -> (match (_67_19) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inl (_67_1705) -> begin
(failwith ("asright"))
end))
in (Support.List.choose (fun ( x ) -> (let _68_26804 = (mlmod1_of_mod1 Struct mlenv x)
in (Support.Option.map asright _68_26804))) modx)))

let mlsig_of_sig = (fun ( mlenv ) ( modx ) -> (let asleft = (fun ( _67_20 ) -> (match (_67_20) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inr (_67_1715) -> begin
(failwith ("asleft"))
end))
in (Support.List.choose (fun ( x ) -> (let _68_26812 = (mlmod1_of_mod1 Sig mlenv x)
in (Support.Option.map asleft _68_26812))) modx)))

let mlmod_of_fstar = (fun ( fmod_ ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _67_1721 = (Support.Microsoft.FStar.Util.fprint1 "OCaml extractor : %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let mod_ = (mlmod_of_mod (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (let sig_ = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (name, sig_, mod_))))))

let mlmod_of_iface = (fun ( fmod_ ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _67_1727 = (Support.Microsoft.FStar.Util.fprint1 "OCaml skip: %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let _68_26817 = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Prims.pipe_right _68_26817 Support.Prims.ignore)))))

let mllib_empty = Microsoft_FStar_Backends_ML_Syntax.MLLib ([])

let rec mllib_add = (fun ( _67_1730 ) ( _67_1734 ) -> (match ((_67_1730, _67_1734)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib), (path, sig_, mod_)) -> begin
(let n = (Support.String.concat "_" (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[])))
in (let rec aux = (fun ( _67_21 ) -> (match (_67_21) with
| [] -> begin
((n, Some ((sig_, mod_)), mllib_empty))::[]
end
| (name, None, sublibs)::tl -> begin
(let the = (name, None, sublibs)
in (match ((name = (Support.Prims.snd path))) with
| true -> begin
((name, Some ((sig_, mod_)), sublibs))::tl
end
| false -> begin
(let _68_26824 = (aux tl)
in (the)::_68_26824)
end))
end
| (name, Some ((ssig, mmod)), sublibs)::tl -> begin
(let the = (name, Some ((ssig, mmod)), sublibs)
in (match ((name = (Support.Prims.snd path))) with
| true -> begin
((name, Some ((ssig, mod_)), sublibs))::tl
end
| false -> begin
(let _68_26825 = (aux tl)
in (the)::_68_26825)
end))
end))
in (let _68_26826 = (aux mllib)
in Microsoft_FStar_Backends_ML_Syntax.MLLib (_68_26826))))
end))

let mlmod_of_fstars = (fun ( fmods ) -> (let in_std_ns = (fun ( x ) -> (let _68_26832 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.Microsoft.FStar.Util.for_some (fun ( y ) -> (in_ns (y, x))) _68_26832)))
in (let fmods = (Support.List.filter (fun ( x ) -> (let _67_1761 = (Support.Microsoft.FStar.Util.fprint1 "Extract module: %s\n" x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (not ((let _68_26835 = (Support.List.map (fun ( y ) -> y.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ns)
in (in_std_ns _68_26835)))))) fmods)
in (let stdlib = (Support.List.map (fun ( x ) -> (Support.Microsoft.FStar.Util.concat_l "." x)) outmod)
in (let extlib = (let _68_26838 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.map (fun ( x ) -> (Support.Microsoft.FStar.Util.concat_l "." x)) _68_26838))
in (let fmods = (Support.List.filter (fun ( x ) -> (not ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str stdlib)))) fmods)
in (let fmods = (Support.List.choose (fun ( x ) -> (match ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str extlib)) with
| true -> begin
(let _67_1772 = (mlmod_of_iface x)
in None)
end
| false -> begin
(let _68_26841 = (mlmod_of_fstar x)
in Some (_68_26841))
end)) fmods)
in (let for1 = (fun ( mllib ) ( the ) -> (let _67_1781 = the
in (match (_67_1781) with
| (path, sig_, mod_) -> begin
(let modname = (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[]))
in (let rec checkname = (fun ( modname ) ( fbd ) -> (match ((modname, fbd)) with
| (_67_1787, []) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(checkname t1 t2)
end
| _67_1798 -> begin
false
end))
in (let aout = (mllib_add mllib the)
in aout)))
end)))
in (Support.List.fold_left for1 mllib_empty fmods)))))))))




