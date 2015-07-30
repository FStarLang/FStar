
type mlenv =
{mle_name : Microsoft_FStar_Backends_ML_Syntax.mlpath}

let is_Mkmlenv = (fun ( _ ) -> (failwith ("Not yet implemented")))

let mk_mlenv = (fun ( name ) -> {mle_name = name})

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Set")::[])::(("Map")::[])::(("Heap")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let record_constructors = (Support.Microsoft.FStar.Util.smap_create 17)

let algebraic_constructors = (Support.Microsoft.FStar.Util.smap_create 40)

let _ign = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors "Prims.Some" (1, ("v")::[]))

let rec in_ns = (fun ( x ) -> (match (x) with
| ([], _) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_, _) -> begin
false
end))

let path_of_ns = (fun ( mlenv ) ( ns ) -> (let ns = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) ns)
in (let outsupport = (fun ( _64_48 ) -> (match (_64_48) with
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
(match ((let _65_25160 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _65_25160))) with
| None -> begin
(outsupport ((Support.List.append (Support.Prims.fst mlenv.mle_name) (((Support.Prims.snd mlenv.mle_name))::[])), ns))
end
| _ -> begin
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
| _ -> begin
(let ns = x.Microsoft_FStar_Absyn_Syntax.ns
in (let x = x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (let _65_25165 = (path_of_ns mlenv ns)
in (_65_25165, x))))
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
| DuplicatedLocal (_) -> begin
"duplicated-local"
end))

let unexpected = (fun ( rg ) ( what ) -> (raise (OCamlFailure ((rg, Unexpected (what))))))

let unsupported = (fun ( rg ) ( what ) -> (raise (OCamlFailure ((rg, Unsupported (what))))))

let unbound_var = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, UnboundVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let unbound_ty_var = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, UnboundTyVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let duplicated_local = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, DuplicatedLocal (x))))))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( x ) -> (let _64_105 = (Support.Microsoft.FStar.Util.incr c)
in (let _65_25218 = (Support.ST.read c)
in (x, _65_25218)))))

let tyvar_of_int = (let tyvars = "abcdefghijklmnopqrstuvwxyz"
in (let rec aux = (fun ( n ) -> (let s = (let _65_25222 = (Support.String.get tyvars (n mod 26))
in (Support.Microsoft.FStar.Util.string_of_char _65_25222))
in (match ((n >= (Support.String.length tyvars))) with
| true -> begin
(let _65_25223 = (aux (n / 26))
in (Support.String.strcat _65_25223 s))
end
| false -> begin
s
end)))
in (fun ( n ) -> (let _65_25225 = (aux n)
in (Support.String.strcat "\'" _65_25225)))))

type lenv =
| LEnv of Microsoft_FStar_Backends_ML_Syntax.mlident Support.Microsoft.FStar.Util.smap

let is_LEnv = (fun ( _discr_ ) -> (match (_discr_) with
| LEnv (_) -> begin
true
end
| _ -> begin
false
end))

let lempty = (let _65_25230 = (Support.Microsoft.FStar.Util.smap_create 0)
in LEnv (_65_25230))

let lenv_of_mlenv = (fun ( _64_113 ) -> lempty)

let lpush = (fun ( _64_116 ) ( real ) ( pp ) -> (match (_64_116) with
| LEnv (lenv) -> begin
(let mlid = (fresh pp.Microsoft_FStar_Absyn_Syntax.idText)
in (let _64_120 = (Support.Microsoft.FStar.Util.smap_add lenv real.Microsoft_FStar_Absyn_Syntax.idText mlid)
in (LEnv (lenv), mlid)))
end))

let lresolve = (fun ( _64_123 ) ( x ) -> (match (_64_123) with
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

let tempty = (let _65_25247 = (Support.Microsoft.FStar.Util.smap_create 0)
in TEnv (_65_25247))

let tvsym = (fun ( _64_131 ) -> (match (_64_131) with
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
(let _65_25255 = (Support.Microsoft.FStar.Util.set_add pp used)
in (_65_25255, pp))
end)))
in (let freshen = (fun ( used ) ( pp ) -> (match (pp) with
| Some (pp) when (not ((Support.Microsoft.FStar.Util.set_mem pp.Microsoft_FStar_Absyn_Syntax.idText used))) -> begin
(let _65_25260 = (Support.Microsoft.FStar.Util.set_add pp.Microsoft_FStar_Absyn_Syntax.idText used)
in (_65_25260, pp.Microsoft_FStar_Absyn_Syntax.idText))
end
| _ -> begin
(fresh_tyvar used 0)
end))
in (let _64_164 = (let for1 = (fun ( used ) ( tv ) -> (match (tv) with
| Some ((real, pp)) -> begin
(let _64_153 = (freshen used (Some (pp)))
in (match (_64_153) with
| (used, pp) -> begin
(let _65_25266 = (let _65_25265 = (fresh pp)
in (_65_25265, Some (real.Microsoft_FStar_Absyn_Syntax.idText)))
in (used, _65_25266))
end))
end
| None -> begin
(let _64_157 = (freshen used None)
in (match (_64_157) with
| (used, pp) -> begin
(let _65_25268 = (let _65_25267 = (fresh pp)
in (_65_25267, None))
in (used, _65_25268))
end))
end))
in (let _65_25272 = (Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> (match ((x = y)) with
| true -> begin
0
end
| false -> begin
1
end)) (fun ( x ) -> 0))
in (Support.Microsoft.FStar.Util.fold_map for1 _65_25272 tvs)))
in (match (_64_164) with
| (_, tvs) -> begin
(let tparams = (Support.List.map (fun ( _64_168 ) -> (match (_64_168) with
| (x, _) -> begin
(tvsym x)
end)) tvs)
in (let tvs = (Support.List.choose (fun ( _64_172 ) -> (match (_64_172) with
| (x, y) -> begin
(match (y) with
| None -> begin
None
end
| Some (y) -> begin
Some ((y, (tvsym x)))
end)
end)) tvs)
in (let _65_25276 = (let _65_25275 = (Support.Microsoft.FStar.Util.smap_of_list tvs)
in TEnv (_65_25275))
in (_65_25276, tparams))))
end)))))

let tvar_of_btvar = (fun ( _64_178 ) ( x ) -> (match (_64_178) with
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
| {Microsoft_FStar_Absyn_Syntax.idText = "Prims"; Microsoft_FStar_Absyn_Syntax.idRange = _}::[] -> begin
true
end
| _ -> begin
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
| _ -> begin
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
| _ -> begin
None
end)
end
| false -> begin
None
end))

let is_etuple = (fun ( e ) -> (match ((let _65_25297 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _65_25297.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(let args = (Support.List.collect (fun ( _64_1 ) -> (match (_64_1) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(e)::[]
end)) args)
in (match ((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) when (k = (Support.List.length args)) -> begin
Some (k)
end
| _ -> begin
None
end))
end
| _ -> begin
None
end))

let is_ptuple = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, _, args)) -> begin
(let args = (Support.Prims.pipe_right args (Support.List.collect (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end
| _ -> begin
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
| _ -> begin
None
end))
end
| _ -> begin
None
end))

let mlkind_of_kind = (fun ( tps ) ( k ) -> (let mltparam_of_tparam = (fun ( _64_2 ) -> (match (_64_2) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}; Microsoft_FStar_Absyn_Syntax.p = _}), _) -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.ppname))
end
| x -> begin
None
end))
in (let rec aux = (fun ( acc ) ( k ) -> (match ((let _65_25312 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _65_25312.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
Some ((Support.List.rev acc))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
Some ((Support.List.rev acc))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (([], k)) -> begin
(aux acc k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (x), _)::rest, k2)) -> begin
(match ((aux [] x.Microsoft_FStar_Absyn_Syntax.sort)) with
| Some ([]) -> begin
(let x = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder (Support.Microsoft.FStar.Util.Inl (x), None))) with
| true -> begin
None
end
| false -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))
end)
in (let _65_25313 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (rest, k2) k.Microsoft_FStar_Absyn_Syntax.pos)
in (aux ((x)::acc) _65_25313)))
end
| _ -> begin
None
end)
end
| _ -> begin
None
end))
in (let aout = (Support.List.choose mltparam_of_tparam tps)
in (let some = (fun ( x ) -> Some (x))
in (let _65_25317 = (let _65_25316 = (Support.List.map some aout)
in (Support.List.rev _65_25316))
in (aux _65_25317 k)))))))

let rec mlty_of_ty_core = (fun ( mlenv ) ( tenv ) ( _64_341 ) -> (match (_64_341) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let ty = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (x) -> begin
(let _65_25333 = (tvar_of_btvar tenv x)
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (_65_25333))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _; Microsoft_FStar_Absyn_Syntax.sort = ty; Microsoft_FStar_Absyn_Syntax.p = _}, _)) -> begin
(mlty_of_ty mlenv tenv (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(mlty_of_ty mlenv tenv (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (([], c)) -> begin
(mlty_of_ty mlenv tenv (rg, (Microsoft_FStar_Absyn_Util.comp_result c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (((Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _}), _)::rest, c)) -> begin
(let t2 = (match (rest) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let mlt1 = (mlty_of_ty mlenv tenv (rg, t1))
in (let mlt2 = (mlty_of_ty mlenv tenv (rg, t2))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((mlt1, Microsoft_FStar_Backends_ML_Syntax.E_IMPURE, mlt2)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (((Support.Microsoft.FStar.Util.Inl (_), _)::rest, c)) -> begin
(let r = (match (rest) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlty_of_ty mlenv tenv (rg, r)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (_) -> begin
(unexpected rg "type-constant")
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, [])) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t1, (Support.Microsoft.FStar.Util.Inl (t2), _)::rest)) -> begin
(let t2 = (match (rest) with
| [] -> begin
t2
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t2, rest) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let mlt1 = (mlty_of_ty mlenv tenv (rg, t1))
in (let mlt2 = (mlty_of_ty mlenv tenv (rg, t2))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((mlt1, mlt2)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, (Support.Microsoft.FStar.Util.Inr (_), _)::rest)) -> begin
(let r = (match (rest) with
| [] -> begin
t
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, rest) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlty_of_ty mlenv tenv (rg, r)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_) -> begin
(unsupported rg "type-fun")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_) -> begin
(unexpected rg "type-meta")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_) -> begin
(unexpected rg "type-uvar")
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(unexpected rg "type-unknown")
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(unexpected rg "type-delayed")
end)))
end))
and maybe_named = (fun ( mlenv ) ( tenv ) ( _64_455 ) -> (match (_64_455) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec aux = (fun ( acc ) ( _64_461 ) -> (match (_64_461) with
| (rg, ty) -> begin
(match ((let _65_25341 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _65_25341.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(let _65_25343 = (let _65_25342 = (mlpath_of_lident mlenv c.Microsoft_FStar_Absyn_Syntax.v)
in (_65_25342, acc))
in Some (_65_25343))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(match ((Support.Prims.pipe_right args (Support.Microsoft.FStar.Util.for_some (fun ( _64_3 ) -> (match (_64_3) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let tys = (Support.Prims.pipe_right args (Support.List.map (fun ( _64_4 ) -> (match (_64_4) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| _ -> begin
(failwith ("impos"))
end))))
in (aux (Support.List.append tys acc) (rg, head)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _; Microsoft_FStar_Absyn_Syntax.sort = ty; Microsoft_FStar_Absyn_Syntax.p = _}, _)) -> begin
(aux acc (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(aux acc (rg, ty))
end
| _ -> begin
None
end)
end))
in (aux [] (rg, ty))))
end))
and maybe_tuple = (fun ( mlenv ) ( tenv ) ( _64_507 ) -> (match (_64_507) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec unfun = (fun ( n ) ( ty ) -> (match ((n <= 0)) with
| true -> begin
Some (ty)
end
| false -> begin
(match ((let _65_25353 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _65_25353.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, ty)) -> begin
(unfun (n - (Support.List.length bs)) ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(unfun n ty)
end
| _ -> begin
None
end)
end))
in (let rec aux = (fun ( acc ) ( ty ) -> (match ((let _65_25358 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _65_25358.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(match ((as_tprims c.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (Tuple (n)) -> begin
(match (((Support.List.length acc) <> n)) with
| true -> begin
None
end
| false -> begin
(let _65_25360 = (Support.List.map (fun ( ty ) -> (mlty_of_ty mlenv tenv (rg, ty))) acc)
in Some (_65_25360))
end)
end
| _ -> begin
None
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(match ((Support.Prims.pipe_right args (Support.Microsoft.FStar.Util.for_some (fun ( _64_5 ) -> (match (_64_5) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let tys = (Support.Prims.pipe_right args (Support.List.map (fun ( _64_6 ) -> (match (_64_6) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
t
end
| _ -> begin
(failwith ("impos"))
end))))
in (aux (Support.List.append tys acc) head))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(aux acc ty)
end
| _ -> begin
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
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((dom, _, codom)) -> begin
(aux ((dom)::acc) codom)
end
| _ -> begin
((Support.List.rev acc), ty)
end))
in (aux [] ty)))

let rec strip_polymorphism = (fun ( acc ) ( rg ) ( ty ) -> (let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (match ((let _65_25375 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _65_25375.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _64_618 = (Support.Prims.pipe_right bs (Support.List.partition (fun ( _64_7 ) -> (match (_64_7) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}; Microsoft_FStar_Absyn_Syntax.p = _}), _) -> begin
true
end
| _ -> begin
false
end))))
in (match (_64_618) with
| (ts, vs) -> begin
(let ts = (Support.Prims.pipe_right ts (Support.List.collect (fun ( _64_8 ) -> (match (_64_8) with
| (Support.Microsoft.FStar.Util.Inl (x), _) -> begin
((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))::[]
end
| _ -> begin
[]
end))))
in (match ((vs, c.Microsoft_FStar_Absyn_Syntax.n)) with
| ([], Microsoft_FStar_Absyn_Syntax.Total (ty)) -> begin
(ts, rg, ty)
end
| ([], Microsoft_FStar_Absyn_Syntax.Comp (c)) -> begin
(ts, rg, c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| (_, _) -> begin
(let _65_25378 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (vs, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
in (ts, rg, _65_25378))
end))
end))
end
| _ -> begin
((Support.List.rev acc), rg, ty)
end)))

let mlscheme_of_ty = (fun ( mlenv ) ( rg ) ( ty ) -> (let _64_649 = (strip_polymorphism [] rg ty)
in (match (_64_649) with
| (tparams, rg, ty) -> begin
(let some = (fun ( x ) -> Some (x))
in (let _64_654 = (let _65_25387 = (Support.List.map some tparams)
in (tenv_of_tvmap _65_25387))
in (match (_64_654) with
| (tenv, tparams) -> begin
(let _65_25388 = (mlty_of_ty mlenv tenv (rg, ty))
in (tparams, _65_25388))
end)))
end)))

let rec mlpat_of_pat = (fun ( mlenv ) ( rg ) ( le ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, _, ps)) -> begin
(let ps = (Support.Prims.pipe_right ps (Support.List.filter (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
false
end
| _ -> begin
true
end))))
in (match (((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v) = Some ((Support.List.length ps)))) with
| true -> begin
(let _64_679 = (Support.Microsoft.FStar.Util.fold_map (fun ( le ) ( pat ) -> (mlpat_of_pat mlenv pat.Microsoft_FStar_Absyn_Syntax.p le pat)) le ps)
in (match (_64_679) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps))
end))
end
| false -> begin
(let _64_682 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_64_682) with
| (le, ps) -> begin
(let p = (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
(let _65_25404 = (let _65_25403 = (path_of_ns mlenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (let _65_25402 = (let _65_25401 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.List.zip _65_25401 ps))
in (_65_25403, _65_25402)))
in Microsoft_FStar_Backends_ML_Syntax.MLP_Record (_65_25404))
end
| None -> begin
(let _65_25406 = (let _65_25405 = (mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v)
in (_65_25405, ps))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_65_25406))
end)
in (le, p))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
(let _64_695 = (lpush le x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_64_695) with
| (le, mlid) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Var (mlid))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _65_25408 = (let _65_25407 = (Microsoft_FStar_Backends_ML_Util.mlconst_of_const c)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Const (_65_25407))
in (le, _65_25408))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _64_702 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_64_702) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_) -> begin
(unsupported rg "top-level-dot-patterns")
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_) -> begin
(unsupported rg "top-level-dot-patterns")
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (_) -> begin
(unsupported rg "pattern-type-variable")
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_) -> begin
(unsupported rg "pattern-type-wild")
end))

let rec mlexpr_of_expr = (fun ( mlenv ) ( rg ) ( lenv ) ( e ) -> (let rg = e.Microsoft_FStar_Absyn_Syntax.pos
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let rec eta_expand_dataconst = (fun ( ct ) ( args ) ( nvars ) -> (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let rec bvs = (fun ( _64_9 ) -> (match (_64_9) with
| 0 -> begin
[]
end
| n -> begin
(let _64_733 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _65_25439 = (let _65_25437 = (let _65_25436 = (let _65_25434 = (let _65_25433 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _65_25433))
in (Support.String.strcat "__dataconst_" _65_25434))
in (let _65_25435 = (Support.ST.read ctr)
in (_65_25436, _65_25435)))
in (_65_25437, None))
in (let _65_25438 = (bvs (n - 1))
in (_65_25439)::_65_25438)))
end))
in (let vs = (bvs nvars)
in (let fapp = (let _65_25443 = (let _65_25442 = (let _65_25441 = (Support.List.map (fun ( _64_739 ) -> (match (_64_739) with
| (x, _) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Var (x)
end)) vs)
in (Support.List.append args _65_25441))
in (ct, _65_25442))
in Microsoft_FStar_Backends_ML_Syntax.MLE_CTor (_65_25443))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((vs, fapp)))))))
in (let mkCTor = (fun ( c ) ( args ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
(let _65_25452 = (let _65_25451 = (path_of_ns mlenv c.Microsoft_FStar_Absyn_Syntax.ns)
in (let _65_25450 = (let _65_25449 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.List.zip _65_25449 args))
in (_65_25451, _65_25450)))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Record (_65_25452))
end
| None -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((n, _)) when (n > (Support.List.length args)) -> begin
(let _65_25453 = (mlpath_of_lident mlenv c)
in (eta_expand_dataconst _65_25453 args (n - (Support.List.length args))))
end
| _ -> begin
(let _65_25455 = (let _65_25454 = (mlpath_of_lident mlenv c)
in (_65_25454, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_CTor (_65_25455))
end)
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((sube, args)) -> begin
(match ((sube.Microsoft_FStar_Absyn_Syntax.n, args)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _::_::(Support.Microsoft.FStar.Util.Inr (a1), _)::a2::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_left") -> begin
(mlexpr_of_expr mlenv rg lenv (let _64_775 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a1, (a2)::[])); Microsoft_FStar_Absyn_Syntax.tk = _64_775.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _64_775.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _64_775.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _64_775.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _::_::a1::(Support.Microsoft.FStar.Util.Inr (a2), _)::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_right") -> begin
(mlexpr_of_expr mlenv rg lenv (let _64_793 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a2, (a1)::[])); Microsoft_FStar_Absyn_Syntax.tk = _64_793.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _64_793.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _64_793.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _64_793.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _) when ((((c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assume") || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assert")) || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.erase")) || (Support.Microsoft.FStar.Util.starts_with c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText "l__")) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Unit)
end
| (_, _) -> begin
(match ((is_etuple e)) with
| Some (k) -> begin
(let args = (Support.List.collect (fun ( _64_10 ) -> (match (_64_10) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _65_25457 = (mlexpr_of_expr mlenv rg lenv e)
in (_65_25457)::[])
end)) args)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (args))
end
| _ -> begin
(let args = (Support.List.collect (fun ( _64_11 ) -> (match (_64_11) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _65_25459 = (mlexpr_of_expr mlenv rg lenv e)
in (_65_25459)::[])
end)) args)
in (match (sube) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)
end
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(let subns = (let _65_25461 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (Support.String.concat "." _65_25461))
in (let _64_873 = (match ((Support.List.rev c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)) with
| [] -> begin
("", [])
end
| h::t -> begin
(h.Microsoft_FStar_Absyn_Syntax.idText, (Support.List.rev t))
end)
in (match (_64_873) with
| (rn, subnsl) -> begin
(match ((let _65_25462 = (Support.Microsoft.FStar.Util.smap_try_find record_constructors subns)
in (_65_25462, args))) with
| (Some (_), arg::[]) -> begin
(let _65_25465 = (let _65_25464 = (let _65_25463 = (path_of_ns mlenv subnsl)
in (_65_25463, c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (arg, _65_25464))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Proj (_65_25465))
end
| (Some (_), arg::args) -> begin
(let _65_25470 = (let _65_25469 = (let _65_25468 = (let _65_25467 = (let _65_25466 = (path_of_ns mlenv subnsl)
in (_65_25466, c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (arg, _65_25467))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Proj (_65_25468))
in (_65_25469, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_65_25470))
end
| _ -> begin
(let _65_25472 = (let _65_25471 = (mlexpr_of_expr mlenv rg lenv sube)
in (_65_25471, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_65_25472))
end)
end)))
end
| _ -> begin
(let _65_25474 = (let _65_25473 = (mlexpr_of_expr mlenv rg lenv sube)
in (_65_25473, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_65_25474))
end))
end)
end)
end
| _ -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _65_25475 = (lresolve lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Var (_65_25475))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) -> begin
(mkCTor x.Microsoft_FStar_Absyn_Syntax.v [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _)) -> begin
(let fid = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (match ((((Support.Microsoft.FStar.Util.starts_with fid "is_") && ((Support.String.length fid) > 3)) && (let _65_25476 = (Support.Microsoft.FStar.Util.char_at fid 3)
in (Support.Microsoft.FStar.Util.is_upper _65_25476)))) with
| true -> begin
(let sub = (Support.Microsoft.FStar.Util.substring_from fid 3)
in (let mlid = (fresh "_discr_")
in (let rid = (let _64_908 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ns = _64_908.Microsoft_FStar_Absyn_Syntax.ns; Microsoft_FStar_Absyn_Syntax.ident = (let _64_910 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = sub; Microsoft_FStar_Absyn_Syntax.idRange = _64_910.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = _64_908.Microsoft_FStar_Absyn_Syntax.nsstr; Microsoft_FStar_Absyn_Syntax.str = sub})
in (let _65_25484 = (let _65_25483 = (let _65_25482 = (let _65_25481 = (let _65_25480 = (let _65_25479 = (let _65_25478 = (let _65_25477 = (mlpath_of_lident mlenv rid)
in (_65_25477, (Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)::[]))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_65_25478))
in (_65_25479, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (true))))
in (_65_25480)::((Microsoft_FStar_Backends_ML_Syntax.MLP_Wild, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (false))))::[])
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_ML_Syntax.idsym mlid))), _65_25481))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match (_65_25482))
in (((mlid, None))::[], _65_25483))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun (_65_25484)))))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr)) with
| Some ((_, projs)) -> begin
(let mlid = (fresh "_proj_")
in (let cargs = (Support.List.map (fun ( x ) -> (let _65_25486 = (fresh x)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Var (_65_25486))) projs)
in (let _64_923 = (Support.List.rev x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_64_923) with
| cn::cr -> begin
(let crstr = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) cr)
in (let rid = {Microsoft_FStar_Absyn_Syntax.ns = cr; Microsoft_FStar_Absyn_Syntax.ident = (let _64_926 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = cn.Microsoft_FStar_Absyn_Syntax.idText; Microsoft_FStar_Absyn_Syntax.idRange = _64_926.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = (Support.String.concat "." crstr); Microsoft_FStar_Absyn_Syntax.str = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr}
in (let cn = cn.Microsoft_FStar_Absyn_Syntax.idText
in (let _65_25495 = (let _65_25494 = (let _65_25493 = (let _65_25492 = (let _65_25491 = (let _65_25490 = (let _65_25489 = (let _65_25488 = (mlpath_of_lident mlenv rid)
in (_65_25488, cargs))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_65_25489))
in (_65_25490, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))))
in (_65_25491)::[])
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_ML_Syntax.idsym mlid))), _65_25492))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match (_65_25493))
in (((mlid, None))::[], _65_25494))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun (_65_25495)))))
end))))
end
| None -> begin
(let _65_25496 = (mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Name (_65_25496))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _65_25497 = (Microsoft_FStar_Backends_ML_Util.mlconst_of_const c)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Const (_65_25497))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (([], e)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inl (_), _)::rest, e)) -> begin
(let _65_25498 = (match ((Support.List.isEmpty rest)) with
| true -> begin
e
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlexpr_of_expr mlenv rg lenv _65_25498))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inr (x), _)::rest, e)) -> begin
(let _64_960 = (lpush lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_64_960) with
| (lenv, mlid) -> begin
(let e = (let _65_25499 = (match ((Support.List.isEmpty rest)) with
| true -> begin
e
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlexpr_of_expr mlenv rg lenv _65_25499))
in (Microsoft_FStar_Backends_ML_Syntax.mlfun mlid e))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((x, (p, None, e)::[])) when (Microsoft_FStar_Absyn_Util.is_wild_pat p) -> begin
(match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| _ -> begin
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
| _ -> begin
(let e = (mlexpr_of_expr mlenv rg lenv e)
in (let bs = (Support.List.map (mlbranch_of_branch mlenv rg lenv) bs)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((e, bs))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((rec_, lb), body)) -> begin
(let _64_1041 = (mllets_of_lets mlenv rg lenv (rec_, lb))
in (match (_64_1041) with
| (lenv, bindings) -> begin
(let body = (mlexpr_of_expr mlenv rg lenv body)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, bindings), body)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let _64_1048 = ()
in (let _64_1071 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(c, args)
end
| _ -> begin
(unexpected rg "meta-data-app-without-fvar")
end)
in (match (_64_1071) with
| (c, args) -> begin
(let args = (Support.Prims.pipe_right args (Support.List.collect (fun ( _64_12 ) -> (match (_64_12) with
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(e)::[]
end
| _ -> begin
[]
end))))
in (let args = (Support.List.map (mlexpr_of_expr mlenv rg lenv) args)
in (mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let d1 = (mlexpr_of_expr mlenv rg lenv e1)
in (let d2 = (mlexpr_of_expr mlenv rg lenv e2)
in (Microsoft_FStar_Backends_ML_Syntax.mlseq d1 d2)))
end
| _ -> begin
(unexpected rg "expr-seq-mark-without-let")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Primop))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.MaskedEffect))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_) -> begin
(unexpected rg "expr-app")
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_) -> begin
(unexpected rg "expr-uvar")
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(unexpected rg "expr-delayed")
end)
end))))))
and mllets_of_lets = (fun ( mlenv ) ( rg ) ( lenv ) ( _64_1137 ) -> (match (_64_1137) with
| (rec_, lbs) -> begin
(let downct = (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(x, lb.Microsoft_FStar_Absyn_Syntax.lbdef)
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(unexpected rg "expr-let-in-with-fvar")
end))
in (let lbs = (Support.List.map downct lbs)
in (let _64_1153 = (Support.Microsoft.FStar.Util.fold_map (fun ( lenv ) ( _64_1150 ) -> (match (_64_1150) with
| (x, _) -> begin
(lpush lenv x.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.ppname)
end)) lenv lbs)
in (match (_64_1153) with
| (lenvb, mlids) -> begin
(let es = (let inlenv = (match (rec_) with
| true -> begin
lenvb
end
| false -> begin
lenv
end)
in (Support.List.map (fun ( _64_1157 ) -> (match (_64_1157) with
| (x, e) -> begin
(let mlid = (lresolve lenvb x.Microsoft_FStar_Absyn_Syntax.realname)
in (let _65_25510 = (mlexpr_of_expr mlenv rg inlenv e)
in {Microsoft_FStar_Backends_ML_Syntax.mllb_name = mlid; Microsoft_FStar_Backends_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Backends_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Backends_ML_Syntax.mllb_def = _65_25510}))
end)) lbs))
in (lenvb, es))
end))))
end))
and mlbranch_of_branch = (fun ( mlenv ) ( rg ) ( lenv ) ( _64_1166 ) -> (match (_64_1166) with
| (pat, when_, body) -> begin
(let _64_1169 = (mlpat_of_pat mlenv rg lenv pat)
in (match (_64_1169) with
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

let mldtype_of_indt = (fun ( mlenv ) ( indt ) -> (let rec getRecordFieldsFromType = (fun ( _64_13 ) -> (match (_64_13) with
| [] -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.RecordType (f)::_ -> begin
Some (f)
end
| _::qualif -> begin
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
(let _65_25558 = (Support.Prims.pipe_right bs (Support.List.collect (fun ( _64_14 ) -> (match (_64_14) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
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
| _ -> begin
[]
end))))
in (let _65_25557 = (comp_vars c.Microsoft_FStar_Absyn_Syntax.n)
in (Support.List.append _65_25558 _65_25557)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t))) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) -> begin
(type_vars t.Microsoft_FStar_Absyn_Syntax.n)
end
| _ -> begin
[]
end))
in (let _64_1331 = (let fold1 = (fun ( sigelt ) ( _64_1260 ) -> (match (_64_1260) with
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
in (let ty = (match ((let _65_25563 = (getRecordFieldsFromType qualif)
in (_65_25563, cs))) with
| (Some (f), c::[]) -> begin
(let fns = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.ident) f)
in (let _64_1281 = (Support.Microsoft.FStar.Util.smap_add record_constructors c.Microsoft_FStar_Absyn_Syntax.str fns)
in (let _65_25567 = (let _65_25566 = (let _65_25565 = (tenv_of_tvmap ar)
in (Support.Prims.snd _65_25565))
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, fns, cs, _65_25566, rg))
in Rec (_65_25567))))
end
| (_, _) -> begin
(let _65_25570 = (let _65_25569 = (let _65_25568 = (tenv_of_tvmap ar)
in (Support.Prims.snd _65_25568))
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, cs, _65_25569, rg))
in DT (_65_25570))
end)
in ((ty)::types, ctors)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, pr, _, _, rg)) -> begin
(let actr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let anames = (let _65_25574 = (type_vars ty.Microsoft_FStar_Absyn_Syntax.n)
in (Support.List.map (fun ( _64_15 ) -> (match (_64_15) with
| None -> begin
(let _64_1302 = (Support.Microsoft.FStar.Util.incr actr)
in (let _65_25573 = (let _65_25572 = (Support.ST.read actr)
in (Support.Microsoft.FStar.Util.string_of_int _65_25572))
in (Support.String.strcat "_" _65_25573)))
end
| Some (x) -> begin
(let _64_1306 = (Support.Microsoft.FStar.Util.incr actr)
in x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end)) _65_25574))
in (let _64_1309 = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.str ((Support.List.length anames), anames))
in (types, ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (ty, pr)))::ctors))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((x, tps, k, body, _, rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _65_25578 = (let _65_25577 = (let _65_25576 = (let _65_25575 = (tenv_of_tvmap ar)
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, body, _65_25575, rg))
in Abb (_65_25576))
in (_65_25577)::types)
in (_65_25578, ctors)))
end
| _ -> begin
(unexpected (Microsoft_FStar_Absyn_Util.range_of_sigelt sigelt) "no-dtype-or-abbrvs-in-bundle")
end)
end))
in (let _64_1328 = (Support.List.fold_right fold1 indt ([], []))
in (match (_64_1328) with
| (ts, cs) -> begin
(let _65_25579 = (Support.Microsoft.FStar.Util.smap_of_list cs)
in (ts, _65_25579))
end)))
in (match (_64_1331) with
| (ts, cs) -> begin
(let cons_args = (fun ( cname ) ( tparams ) ( rg ) ( x ) -> (let _64_1340 = (let _65_25588 = (Support.Microsoft.FStar.Util.smap_try_find cs cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.Prims.pipe_right _65_25588 Support.Microsoft.FStar.Util.must))
in (match (_64_1340) with
| (c, _) -> begin
(let _64_1344 = (strip_polymorphism [] rg c)
in (match (_64_1344) with
| (cparams, rgty, c) -> begin
(let _64_1345 = (match (((Support.List.length cparams) <> (Support.List.length tparams))) with
| true -> begin
(unexpected rg "invalid-number-of-ctor-params")
end
| false -> begin
()
end)
in (let cparams = (Support.List.map (fun ( _64_1350 ) -> (match (_64_1350) with
| (x, _) -> begin
x.Microsoft_FStar_Absyn_Syntax.idText
end)) cparams)
in (let tenv = (Support.List.zip cparams tparams)
in (let tenv = (let _65_25590 = (Support.Microsoft.FStar.Util.smap_of_list tenv)
in TEnv (_65_25590))
in (let c = (mlty_of_ty mlenv tenv (rgty, c))
in (let _64_1357 = (mltycons_of_mlty c)
in (match (_64_1357) with
| (args, name) -> begin
(match (name) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((tyargs, name)) when ((Support.Prims.snd name) = x) -> begin
(let check = (fun ( x ) ( mty ) -> (match (mty) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (mtyx) -> begin
(x = mtyx)
end
| _ -> begin
false
end))
in (let _64_1369 = (match (((Support.List.length tyargs) <> (Support.List.length cparams))) with
| true -> begin
(unexpected rg "dtype-invalid-ctor-result")
end
| false -> begin
()
end)
in (let _64_1371 = (match ((not ((Support.List.forall2 check tparams tyargs)))) with
| true -> begin
(unsupported rg "dtype-invalid-ctor-result")
end
| false -> begin
()
end)
in args)))
end
| _ -> begin
(unexpected rg "dtype-invalid-ctor-result")
end)
end)))))))
end))
end)))
in (let fortype = (fun ( ty ) -> (match (ty) with
| DT ((x, tcs, tparams, rg)) -> begin
(let mldcons_of_cons = (fun ( cname ) -> (let args = (cons_args cname tparams rg x)
in (cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))
in (let _65_25600 = (let _65_25599 = (Support.List.map mldcons_of_cons tcs)
in Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (_65_25599))
in (x, tparams, _65_25600)))
end
| Rec ((x, f, tcs, tparams, rg)) -> begin
(let args = (match (tcs) with
| cname::[] -> begin
(cons_args cname tparams rg x)
end
| _ -> begin
(unexpected rg "records-should-have-one-single-constructor")
end)
in (let mldproj_of_proj = (fun ( name ) ( c ) -> (name.Microsoft_FStar_Absyn_Syntax.idText, c))
in (let _64_1402 = (match (((Support.List.length f) <> (Support.List.length args))) with
| true -> begin
(let _65_25611 = (let _65_25610 = (let _65_25605 = (Support.List.hd tcs)
in _65_25605.Microsoft_FStar_Absyn_Syntax.str)
in (let _65_25609 = (let _65_25607 = (Support.List.map (fun ( f ) -> f.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.Prims.pipe_right _65_25607 (Support.String.concat ", ")))
in (let _65_25608 = (Support.Prims.pipe_right (Support.List.length args) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format4 "%s, %s, %s fields, %s args" x _65_25610 _65_25609 _65_25608))))
in (unexpected rg _65_25611))
end
| false -> begin
()
end)
in (let _65_25613 = (let _65_25612 = (Support.List.map2 mldproj_of_proj f args)
in Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (_65_25612))
in (x, tparams, _65_25613)))))
end
| Abb ((x, body, (tenv, tparams), rg)) -> begin
(let body = (mlty_of_ty mlenv tenv (rg, body))
in (x, tparams, Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (body)))
end))
in (Support.List.map fortype ts)))
end)))))

let mlmod1_of_mod1 = (fun ( mode ) ( mlenv ) ( modx ) -> (let export_val = (fun ( qal ) -> (let export_val1 = (fun ( _64_16 ) -> (match (_64_16) with
| (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) | (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Private) -> begin
false
end
| _ -> begin
true
end))
in (Support.List.for_all export_val1 qal)))
in (match (modx) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when ((export_val qal) && (mode = Sig)) -> begin
(let _64_1441 = (mlscheme_of_ty mlenv rg ty)
in (match (_64_1441) with
| (tparams, ty) -> begin
Some (Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (tparams, ty)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when (mode = Sig) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((rec_, lbs), rg, _, _)) when (mode = Struct) -> begin
(let downct = (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(x, lb.Microsoft_FStar_Absyn_Syntax.lbdef)
end
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(unexpected rg "expr-top-let-with-bvar")
end))
in (let lbs = (Support.List.map downct lbs)
in (let lbs = (Support.List.map (fun ( _64_1468 ) -> (match (_64_1468) with
| (x, e) -> begin
(let _65_25627 = (mlexpr_of_expr mlenv rg (lenv_of_mlenv mlenv) e)
in {Microsoft_FStar_Backends_ML_Syntax.mllb_name = (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (- (1))); Microsoft_FStar_Backends_ML_Syntax.mllb_tysc = None; Microsoft_FStar_Backends_ML_Syntax.mllb_add_unit = false; Microsoft_FStar_Backends_ML_Syntax.mllb_def = _65_25627})
end)) lbs)
in Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lbs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, rg)) when (mode = Struct) -> begin
(let lenv = (lenv_of_mlenv mlenv)
in (let _65_25630 = (let _65_25629 = (let _65_25628 = (mlexpr_of_expr mlenv rg lenv e)
in Microsoft_FStar_Backends_ML_Syntax.MLM_Top (_65_25628))
in Support.Microsoft.FStar.Util.Inr (_65_25629))
in Some (_65_25630)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, qal, _)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((t, tps, k, ty, _, rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _64_1503 = (tenv_of_tvmap ar)
in (match (_64_1503) with
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
in (let _64_1521 = (tenv_of_tvmap ar)
in (match (_64_1521) with
| (_tenv, tparams) -> begin
Some ((mlitem1_ty mode (((t.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, tparams, None))::[])))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, _, qal, _, _))::[], _, _, _)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, (tx, _, _), qal, _, rg))::[], _, _, _)) when ((as_tprims tx) = Some (Exn)) -> begin
(let rec aux = (fun ( acc ) ( ty ) -> (match ((let _65_25635 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _65_25635.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let tys = (Support.Prims.pipe_right bs (Support.List.collect (fun ( _64_17 ) -> (match (_64_17) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort)::[]
end))))
in tys)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (x) when ((as_tprims x.Microsoft_FStar_Absyn_Syntax.v) = Some (Exn)) -> begin
(Support.List.rev acc)
end
| _ -> begin
(unexpected rg "invalid-exn-type")
end))
in (let args = (aux [] ty)
in (let tenv = (let _65_25637 = (tenv_of_tvmap [])
in (Support.Prims.fst _65_25637))
in (let args = (Support.List.map (fun ( ty ) -> (mlty_of_ty mlenv tenv (rg, ty))) args)
in Some ((mlitem1_exn mode (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((indt, _, _, _)) -> begin
(let aout = (mldtype_of_indt mlenv indt)
in (let aout = (Support.List.map (fun ( _64_1620 ) -> (match (_64_1620) with
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
| Microsoft_FStar_Absyn_Syntax.Sig_assume (_) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (_) -> begin
None
end)))

let mlmod_of_mod = (fun ( mlenv ) ( modx ) -> (let asright = (fun ( _64_18 ) -> (match (_64_18) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(failwith ("asright"))
end))
in (Support.List.choose (fun ( x ) -> (let _65_25647 = (mlmod1_of_mod1 Struct mlenv x)
in (Support.Option.map asright _65_25647))) modx)))

let mlsig_of_sig = (fun ( mlenv ) ( modx ) -> (let asleft = (fun ( _64_19 ) -> (match (_64_19) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(failwith ("asleft"))
end))
in (Support.List.choose (fun ( x ) -> (let _65_25655 = (mlmod1_of_mod1 Sig mlenv x)
in (Support.Option.map asleft _65_25655))) modx)))

let mlmod_of_fstar = (fun ( fmod_ ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _64_1664 = (Support.Microsoft.FStar.Util.fprint1 "OCaml extractor : %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let mod_ = (mlmod_of_mod (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (let sig_ = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (name, sig_, mod_))))))

let mlmod_of_iface = (fun ( fmod_ ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _64_1670 = (Support.Microsoft.FStar.Util.fprint1 "OCaml skip: %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let _65_25660 = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Prims.pipe_right _65_25660 Support.Prims.ignore)))))

let mllib_empty = Microsoft_FStar_Backends_ML_Syntax.MLLib ([])

let rec mllib_add = (fun ( _64_1673 ) ( _64_1677 ) -> (match ((_64_1673, _64_1677)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib), (path, sig_, mod_)) -> begin
(let n = (Support.String.concat "_" (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[])))
in (let rec aux = (fun ( _64_20 ) -> (match (_64_20) with
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
(let _65_25665 = (aux tl)
in (the)::_65_25665)
end))
end
| (name, Some ((ssig, mmod)), sublibs)::tl -> begin
(let the = (name, Some ((ssig, mmod)), sublibs)
in (match ((name = (Support.Prims.snd path))) with
| true -> begin
((name, Some ((ssig, mod_)), sublibs))::tl
end
| false -> begin
(let _65_25666 = (aux tl)
in (the)::_65_25666)
end))
end))
in (failwith ("to be fixed"))))
end))

let mlmod_of_fstars = (fun ( fmods ) -> (let in_std_ns = (fun ( x ) -> (let _65_25672 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.Microsoft.FStar.Util.for_some (fun ( y ) -> (in_ns (y, x))) _65_25672)))
in (let fmods = (Support.List.filter (fun ( x ) -> (let _64_1704 = (Support.Microsoft.FStar.Util.fprint1 "Extract module: %s\n" x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (not ((let _65_25675 = (Support.List.map (fun ( y ) -> y.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ns)
in (in_std_ns _65_25675)))))) fmods)
in (let stdlib = (Support.List.map (fun ( x ) -> (Support.Microsoft.FStar.Util.concat_l "." x)) outmod)
in (let extlib = (let _65_25678 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.map (fun ( x ) -> (Support.Microsoft.FStar.Util.concat_l "." x)) _65_25678))
in (let fmods = (Support.List.filter (fun ( x ) -> (not ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str stdlib)))) fmods)
in (let fmods = (Support.List.choose (fun ( x ) -> (match ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str extlib)) with
| true -> begin
(let _64_1715 = (mlmod_of_iface x)
in None)
end
| false -> begin
(let _65_25681 = (mlmod_of_fstar x)
in Some (_65_25681))
end)) fmods)
in (let for1 = (fun ( mllib ) ( the ) -> (let _64_1724 = the
in (match (_64_1724) with
| (path, sig_, mod_) -> begin
(let modname = (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[]))
in (let rec checkname = (fun ( modname ) ( fbd ) -> (match ((modname, fbd)) with
| (_, []) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(checkname t1 t2)
end
| _ -> begin
false
end))
in (let aout = (mllib_add mllib the)
in aout)))
end)))
in (Support.List.fold_left for1 mllib_empty fmods)))))))))




