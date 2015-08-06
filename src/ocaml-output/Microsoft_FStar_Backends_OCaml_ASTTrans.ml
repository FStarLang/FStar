
type mlenv =
{mle_name : Microsoft_FStar_Backends_ML_Syntax.mlpath}

let is_Mkmlenv = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkmlenv"))

let mk_mlenv = (fun ( name ) -> {mle_name = name})

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Set")::[])::(("Map")::[])::(("Heap")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let record_constructors = (Support.Microsoft.FStar.Util.smap_create 17)

let algebraic_constructors = (Support.Microsoft.FStar.Util.smap_create 40)

let _ign = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors "Prims.Some" (1, ("v")::[]))

let rec in_ns = (fun ( _69_1 ) -> (match (_69_1) with
| ([], _69_28) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(Obj.magic in_ns)
end
| (_69_38, _69_40) -> begin
false
end))

let path_of_ns = (fun ( mlenv ) ( ns ) -> (let ns = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) ns)
in (let outsupport = (fun ( _69_48 ) -> (match (_69_48) with
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
(match ((let _70_26429 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _70_26429))) with
| None -> begin
(outsupport ((Support.List.append (Support.Prims.fst mlenv.mle_name) (((Support.Prims.snd mlenv.mle_name))::[])), ns))
end
| _69_55 -> begin
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
| _69_67 -> begin
(let ns = x.Microsoft_FStar_Absyn_Syntax.ns
in (let x = x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (let _70_26434 = (path_of_ns mlenv ns)
in (_70_26434, x))))
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
| DuplicatedLocal (_69_91) -> begin
"duplicated-local"
end))

let unexpected = (fun ( rg ) ( what ) -> (raise (OCamlFailure ((rg, Unexpected (what))))))

let unsupported = (fun ( rg ) ( what ) -> (raise (OCamlFailure ((rg, Unsupported (what))))))

let unbound_var = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, UnboundVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let unbound_ty_var = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, UnboundTyVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let duplicated_local = (fun ( rg ) ( x ) -> (raise (OCamlFailure ((rg, DuplicatedLocal (x))))))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( x ) -> (let _69_105 = (Support.Microsoft.FStar.Util.incr c)
in (let _70_26487 = (Support.ST.read c)
in (x, _70_26487)))))

let tyvar_of_int = (let tyvars = "abcdefghijklmnopqrstuvwxyz"
in (let rec aux = (fun ( n ) -> (let s = (let _70_26491 = (Support.String.get tyvars (n mod 26))
in (Support.Microsoft.FStar.Util.string_of_char _70_26491))
in (match ((n >= (Support.String.length tyvars))) with
| true -> begin
(let _70_26492 = (aux (n / 26))
in (Support.String.strcat _70_26492 s))
end
| false -> begin
s
end)))
in (fun ( n ) -> (let _70_26494 = (aux n)
in (Support.String.strcat "\'" _70_26494)))))

type lenv =
| LEnv of Microsoft_FStar_Backends_ML_Syntax.mlident Support.Microsoft.FStar.Util.smap

let is_LEnv = (fun ( _discr_ ) -> (match (_discr_) with
| LEnv (_) -> begin
true
end
| _ -> begin
false
end))

let lempty = (let _70_26499 = (Support.Microsoft.FStar.Util.smap_create 0)
in LEnv (_70_26499))

let lenv_of_mlenv = (fun ( _69_113 ) -> lempty)

let lpush = (fun ( _69_116 ) ( real ) ( pp ) -> (match (_69_116) with
| LEnv (lenv) -> begin
(let mlid = (fresh pp.Microsoft_FStar_Absyn_Syntax.idText)
in (let _69_120 = (Support.Microsoft.FStar.Util.smap_add lenv real.Microsoft_FStar_Absyn_Syntax.idText mlid)
in (LEnv (lenv), mlid)))
end))

let lresolve = (fun ( _69_123 ) ( x ) -> (match (_69_123) with
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

let tempty = (let _70_26516 = (Support.Microsoft.FStar.Util.smap_create 0)
in TEnv (_70_26516))

let tvsym = (fun ( _69_131 ) -> (match (_69_131) with
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
(let _70_26524 = (Support.Microsoft.FStar.Util.set_add pp used)
in (_70_26524, pp))
end)))
in (let freshen = (fun ( used ) ( pp ) -> (match (pp) with
| Some (pp) when (not ((Support.Microsoft.FStar.Util.set_mem pp.Microsoft_FStar_Absyn_Syntax.idText used))) -> begin
(let _70_26529 = (Support.Microsoft.FStar.Util.set_add pp.Microsoft_FStar_Absyn_Syntax.idText used)
in (_70_26529, pp.Microsoft_FStar_Absyn_Syntax.idText))
end
| _69_143 -> begin
(fresh_tyvar used 0)
end))
in (let _69_164 = (let for1 = (fun ( used ) ( tv ) -> (match (tv) with
| Some ((real, pp)) -> begin
(let _69_153 = (freshen used (Some (pp)))
in (match (_69_153) with
| (used, pp) -> begin
(let _70_26535 = (let _70_26534 = (fresh pp)
in (_70_26534, Some (real.Microsoft_FStar_Absyn_Syntax.idText)))
in (used, _70_26535))
end))
end
| None -> begin
(let _69_157 = (freshen used None)
in (match (_69_157) with
| (used, pp) -> begin
(let _70_26537 = (let _70_26536 = (fresh pp)
in (_70_26536, None))
in (used, _70_26537))
end))
end))
in (let _70_26541 = (Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> (match ((x = y)) with
| true -> begin
0
end
| false -> begin
1
end)) (fun ( x ) -> 0))
in (Support.Microsoft.FStar.Util.fold_map for1 _70_26541 tvs)))
in (match (_69_164) with
| (_69_162, tvs) -> begin
(let tparams = (Support.List.map (fun ( _69_168 ) -> (match (_69_168) with
| (x, _69_167) -> begin
(tvsym x)
end)) tvs)
in (let tvs = (Support.List.choose (fun ( _69_172 ) -> (match (_69_172) with
| (x, y) -> begin
(match (y) with
| None -> begin
None
end
| Some (y) -> begin
Some ((y, (tvsym x)))
end)
end)) tvs)
in (let _70_26545 = (let _70_26544 = (Support.Microsoft.FStar.Util.smap_of_list tvs)
in TEnv (_70_26544))
in (_70_26545, tparams))))
end)))))

let tvar_of_btvar = (fun ( _69_178 ) ( x ) -> (match (_69_178) with
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
| {Microsoft_FStar_Absyn_Syntax.idText = "Prims"; Microsoft_FStar_Absyn_Syntax.idRange = _69_186}::[] -> begin
true
end
| _69_191 -> begin
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
| _69_209 -> begin
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
| _69_224 -> begin
None
end)
end
| false -> begin
None
end))

let is_etuple = (fun ( e ) -> (match ((let _70_26566 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _70_26566.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _69_236)); Microsoft_FStar_Absyn_Syntax.tk = _69_233; Microsoft_FStar_Absyn_Syntax.pos = _69_231; Microsoft_FStar_Absyn_Syntax.fvs = _69_229; Microsoft_FStar_Absyn_Syntax.uvs = _69_227}, args)) -> begin
(let args = (Support.List.collect (fun ( _69_2 ) -> (match (_69_2) with
| (Support.Microsoft.FStar.Util.Inl (_69_245), _69_248) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _69_253) -> begin
(e)::[]
end)) args)
in (match ((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) when (k = (Support.List.length args)) -> begin
Some (k)
end
| _69_259 -> begin
None
end))
end
| _69_261 -> begin
None
end))

let is_ptuple = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, _69_265, args)) -> begin
(let args = (Support.All.pipe_right args (Support.List.collect (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end
| _69_277 -> begin
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
| _69_282 -> begin
None
end))
end
| _69_284 -> begin
None
end))

let mlkind_of_kind = (fun ( tps ) ( k ) -> (let mltparam_of_tparam = (fun ( _69_3 ) -> (match (_69_3) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _69_297; Microsoft_FStar_Absyn_Syntax.pos = _69_295; Microsoft_FStar_Absyn_Syntax.fvs = _69_293; Microsoft_FStar_Absyn_Syntax.uvs = _69_291}; Microsoft_FStar_Absyn_Syntax.p = _69_289}), _69_304) -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.ppname))
end
| x -> begin
None
end))
in (let rec aux = (fun ( acc ) ( k ) -> (match ((let _70_26581 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_26581.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
Some ((Support.List.rev acc))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
Some ((Support.List.rev acc))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (([], k)) -> begin
(aux acc k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (x), _69_321)::rest, k2)) -> begin
(match ((aux [] x.Microsoft_FStar_Absyn_Syntax.sort)) with
| Some ([]) -> begin
(let x = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder (Support.Microsoft.FStar.Util.Inl (x), None))) with
| true -> begin
None
end
| false -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))
end)
in (let _70_26582 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (rest, k2) k.Microsoft_FStar_Absyn_Syntax.pos)
in (aux ((x)::acc) _70_26582)))
end
| _69_331 -> begin
None
end)
end
| _69_333 -> begin
None
end))
in (let aout = (Support.List.choose mltparam_of_tparam tps)
in (let some = (fun ( x ) -> Some (x))
in (let _70_26586 = (let _70_26585 = (Support.List.map some aout)
in (Support.List.rev _70_26585))
in (aux _70_26586 k)))))))

let rec mlty_of_ty_core = (fun ( mlenv ) ( tenv ) ( _69_341 ) -> (match (_69_341) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let ty = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (x) -> begin
(let _70_26602 = (tvar_of_btvar tenv x)
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (_70_26602))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _69_350; Microsoft_FStar_Absyn_Syntax.sort = ty; Microsoft_FStar_Absyn_Syntax.p = _69_347}, _69_353)) -> begin
(mlty_of_ty mlenv tenv (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _69_358)) -> begin
(mlty_of_ty mlenv tenv (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (([], c)) -> begin
(mlty_of_ty mlenv tenv (rg, (Microsoft_FStar_Absyn_Util.comp_result c)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (((Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _69_367}), _69_373)::rest, c)) -> begin
(let t2 = (match (rest) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _69_381 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let mlt1 = (mlty_of_ty mlenv tenv (rg, t1))
in (let mlt2 = (mlty_of_ty mlenv tenv (rg, t2))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((mlt1, Microsoft_FStar_Backends_ML_Syntax.Keep, mlt2)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (((Support.Microsoft.FStar.Util.Inl (_69_387), _69_390)::rest, c)) -> begin
(let r = (match (rest) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _69_398 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlty_of_ty mlenv tenv (rg, r)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (_69_401) -> begin
(unexpected rg "type-constant")
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, [])) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t1, (Support.Microsoft.FStar.Util.Inl (t2), _69_412)::rest)) -> begin
(let t2 = (match (rest) with
| [] -> begin
t2
end
| _69_419 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t2, rest) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let mlt1 = (mlty_of_ty mlenv tenv (rg, t1))
in (let mlt2 = (mlty_of_ty mlenv tenv (rg, t2))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((mlt1, mlt2)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, (Support.Microsoft.FStar.Util.Inr (_69_426), _69_429)::rest)) -> begin
(let r = (match (rest) with
| [] -> begin
t
end
| _69_436 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, rest) None ty.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlty_of_ty mlenv tenv (rg, r)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_69_439) -> begin
(unsupported rg "type-fun")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_69_442) -> begin
(unexpected rg "type-meta")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_69_445) -> begin
(unexpected rg "type-uvar")
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(unexpected rg "type-unknown")
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_69_449) -> begin
(unexpected rg "type-delayed")
end)))
end))
and maybe_named = (fun ( mlenv ) ( tenv ) ( _69_455 ) -> (match (_69_455) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec aux = (fun ( acc ) ( _69_461 ) -> (match (_69_461) with
| (rg, ty) -> begin
(match ((let _70_26613 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _70_26613.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(let _70_26615 = (let _70_26614 = (mlpath_of_lident mlenv c.Microsoft_FStar_Absyn_Syntax.v)
in (_70_26614, acc))
in Some (_70_26615))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(match ((Support.All.pipe_right args (Support.Microsoft.FStar.Util.for_some (fun ( _69_4 ) -> (match (_69_4) with
| (Support.Microsoft.FStar.Util.Inr (_69_470), _69_473) -> begin
true
end
| _69_476 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let tys = (Support.All.pipe_right args (Support.List.map (fun ( _69_5 ) -> (match (_69_5) with
| (Support.Microsoft.FStar.Util.Inl (t), _69_481) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| _69_484 -> begin
(Support.All.failwith "impos")
end))))
in (aux (Support.List.append tys acc) (rg, head)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _69_490; Microsoft_FStar_Absyn_Syntax.sort = ty; Microsoft_FStar_Absyn_Syntax.p = _69_487}, _69_493)) -> begin
(aux acc (rg, ty))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _69_498)) -> begin
(aux acc (rg, ty))
end
| _69_502 -> begin
None
end)
end))
in (aux [] (rg, ty))))
end))
and maybe_tuple = (fun ( mlenv ) ( tenv ) ( _69_507 ) -> (match (_69_507) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec unfun = (fun ( n ) ( ty ) -> (match ((n <= 0)) with
| true -> begin
Some (ty)
end
| false -> begin
(match ((let _70_26625 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _70_26625.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, ty)) -> begin
(unfun (n - (Support.List.length bs)) ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _69_518)) -> begin
(unfun n ty)
end
| _69_522 -> begin
None
end)
end))
in (let rec aux = (fun ( acc ) ( ty ) -> (match ((let _70_26630 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _70_26630.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(match ((as_tprims c.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (Tuple (n)) -> begin
(match (((Support.List.length acc) <> n)) with
| true -> begin
None
end
| false -> begin
(let _70_26632 = (Support.List.map (fun ( ty ) -> (mlty_of_ty mlenv tenv (rg, ty))) acc)
in Some (_70_26632))
end)
end
| _69_533 -> begin
None
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(match ((Support.All.pipe_right args (Support.Microsoft.FStar.Util.for_some (fun ( _69_6 ) -> (match (_69_6) with
| (Support.Microsoft.FStar.Util.Inr (_69_540), _69_543) -> begin
true
end
| (Support.Microsoft.FStar.Util.Inl (t), _69_548) -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let tys = (Support.All.pipe_right args (Support.List.map (fun ( _69_7 ) -> (match (_69_7) with
| (Support.Microsoft.FStar.Util.Inl (t), _69_554) -> begin
t
end
| _69_557 -> begin
(Support.All.failwith "impos")
end))))
in (aux (Support.List.append tys acc) head))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _69_561)) -> begin
(aux acc ty)
end
| _69_565 -> begin
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
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((dom, _69_581, codom)) -> begin
(aux ((dom)::acc) codom)
end
| _69_586 -> begin
((Support.List.rev acc), ty)
end))
in (aux [] ty)))

let rec strip_polymorphism = (fun ( acc ) ( rg ) ( ty ) -> (let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (match ((let _70_26647 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _70_26647.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _69_618 = (Support.All.pipe_right bs (Support.List.partition (fun ( _69_8 ) -> (match (_69_8) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _69_605; Microsoft_FStar_Absyn_Syntax.pos = _69_603; Microsoft_FStar_Absyn_Syntax.fvs = _69_601; Microsoft_FStar_Absyn_Syntax.uvs = _69_599}; Microsoft_FStar_Absyn_Syntax.p = _69_597}), _69_612) -> begin
true
end
| _69_615 -> begin
false
end))))
in (match (_69_618) with
| (ts, vs) -> begin
(let ts = (Support.All.pipe_right ts (Support.List.collect (fun ( _69_9 ) -> (match (_69_9) with
| (Support.Microsoft.FStar.Util.Inl (x), _69_623) -> begin
((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))::[]
end
| _69_626 -> begin
[]
end))))
in (match ((vs, c.Microsoft_FStar_Absyn_Syntax.n)) with
| ([], Microsoft_FStar_Absyn_Syntax.Total (ty)) -> begin
(ts, rg, ty)
end
| ([], Microsoft_FStar_Absyn_Syntax.Comp (c)) -> begin
(ts, rg, c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| (_69_637, _69_639) -> begin
(let _70_26650 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (vs, c) None ty.Microsoft_FStar_Absyn_Syntax.pos)
in (ts, rg, _70_26650))
end))
end))
end
| _69_642 -> begin
((Support.List.rev acc), rg, ty)
end)))

let mlscheme_of_ty = (fun ( mlenv ) ( rg ) ( ty ) -> (let _69_649 = (strip_polymorphism [] rg ty)
in (match (_69_649) with
| (tparams, rg, ty) -> begin
(let some = (fun ( x ) -> Some (x))
in (let _69_654 = (let _70_26659 = (Support.List.map some tparams)
in (tenv_of_tvmap _70_26659))
in (match (_69_654) with
| (tenv, tparams) -> begin
(let _70_26660 = (mlty_of_ty mlenv tenv (rg, ty))
in (tparams, _70_26660))
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
(let _70_26664 = (let _70_26663 = (Support.Microsoft.FStar.Util.int_of_string c)
in (Support.Microsoft.FStar.Util.int32_of_int _70_26663))
in Microsoft_FStar_Backends_ML_Syntax.MLC_Int32 (_70_26664))
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
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((bytes, _69_673)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Bytes (bytes)
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _69_678)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_String ((Support.Microsoft.FStar.Util.string_of_unicode bytes))
end))

let rec mlpat_of_pat = (fun ( mlenv ) ( rg ) ( le ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, _69_687, ps)) -> begin
(let ps = (Support.All.pipe_right ps (Support.List.filter (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
false
end
| _69_699 -> begin
true
end))))
in (match (((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v) = Some ((Support.List.length ps)))) with
| true -> begin
(let _69_705 = (Support.Microsoft.FStar.Util.fold_map (fun ( le ) ( pat ) -> (mlpat_of_pat mlenv pat.Microsoft_FStar_Absyn_Syntax.p le pat)) le ps)
in (match (_69_705) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps))
end))
end
| false -> begin
(let _69_708 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_69_708) with
| (le, ps) -> begin
(let p = (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
(let _70_26680 = (let _70_26679 = (path_of_ns mlenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (let _70_26678 = (let _70_26677 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.List.zip _70_26677 ps))
in (_70_26679, _70_26678)))
in Microsoft_FStar_Backends_ML_Syntax.MLP_Record (_70_26680))
end
| None -> begin
(let _70_26682 = (let _70_26681 = (mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v)
in (_70_26681, ps))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_70_26682))
end)
in (le, p))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _69_716)) -> begin
(let _69_721 = (lpush le x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_69_721) with
| (le, mlid) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Var (mlid))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _70_26684 = (let _70_26683 = (mlconst_of_const c)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Const (_70_26683))
in (le, _70_26684))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _69_728 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_69_728) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_69_730) -> begin
(le, Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_69_733) -> begin
(unsupported rg "top-level-dot-patterns")
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_69_736) -> begin
(unsupported rg "top-level-dot-patterns")
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (_69_739) -> begin
(unsupported rg "pattern-type-variable")
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_69_742) -> begin
(unsupported rg "pattern-type-wild")
end))

let rec mlexpr_of_expr = (fun ( mlenv ) ( rg ) ( lenv ) ( e ) -> (let rg = e.Microsoft_FStar_Absyn_Syntax.pos
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let rec eta_expand_dataconst = (fun ( ct ) ( args ) ( nvars ) -> (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let rec bvs = (fun ( _69_10 ) -> (match (_69_10) with
| 0 -> begin
[]
end
| n -> begin
(let _69_759 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_26715 = (let _70_26713 = (let _70_26712 = (let _70_26710 = (let _70_26709 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _70_26709))
in (Support.String.strcat "__dataconst_" _70_26710))
in (let _70_26711 = (Support.ST.read ctr)
in (_70_26712, _70_26711)))
in (_70_26713, None))
in (let _70_26714 = (bvs (n - 1))
in (_70_26715)::_70_26714)))
end))
in (let vs = (bvs nvars)
in (let fapp = (let _70_26719 = (let _70_26718 = (let _70_26717 = (Support.List.map (fun ( _69_765 ) -> (match (_69_765) with
| (x, _69_764) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Var (x)
end)) vs)
in (Support.List.append args _70_26717))
in (ct, _70_26718))
in Microsoft_FStar_Backends_ML_Syntax.MLE_CTor (_70_26719))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((vs, fapp)))))))
in (let mkCTor = (fun ( c ) ( args ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
(let _70_26728 = (let _70_26727 = (path_of_ns mlenv c.Microsoft_FStar_Absyn_Syntax.ns)
in (let _70_26726 = (let _70_26725 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.List.zip _70_26725 args))
in (_70_26727, _70_26726)))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Record (_70_26728))
end
| None -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((n, _69_776)) when (n > (Support.List.length args)) -> begin
(let _70_26729 = (mlpath_of_lident mlenv c)
in (eta_expand_dataconst _70_26729 args (n - (Support.List.length args))))
end
| _69_780 -> begin
(let _70_26731 = (let _70_26730 = (mlpath_of_lident mlenv c)
in (_70_26730, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_CTor (_70_26731))
end)
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((sube, args)) -> begin
(match ((sube.Microsoft_FStar_Absyn_Syntax.n, args)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _69_798::_69_796::(Support.Microsoft.FStar.Util.Inr (a1), _69_793)::a2::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_left") -> begin
(mlexpr_of_expr mlenv rg lenv (let _69_801 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a1, (a2)::[])); Microsoft_FStar_Absyn_Syntax.tk = _69_801.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _69_801.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _69_801.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _69_801.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _69_816::_69_814::a1::(Support.Microsoft.FStar.Util.Inr (a2), _69_810)::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_right") -> begin
(mlexpr_of_expr mlenv rg lenv (let _69_819 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a2, (a1)::[])); Microsoft_FStar_Absyn_Syntax.tk = _69_819.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _69_819.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _69_819.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _69_819.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, None)), _69_826) when ((((c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assume") || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assert")) || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.erase")) || (Support.Microsoft.FStar.Util.starts_with c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText "l__")) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Unit)
end
| (_69_829, _69_831) -> begin
(match ((is_etuple e)) with
| Some (k) -> begin
(let args = (Support.List.collect (fun ( _69_11 ) -> (match (_69_11) with
| (Support.Microsoft.FStar.Util.Inl (_69_837), _69_840) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _69_845) -> begin
(let _70_26733 = (mlexpr_of_expr mlenv rg lenv e)
in (_70_26733)::[])
end)) args)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (args))
end
| _69_849 -> begin
(let args = (Support.List.collect (fun ( _69_12 ) -> (match (_69_12) with
| (Support.Microsoft.FStar.Util.Inl (_69_852), _69_855) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _69_860) -> begin
(let _70_26735 = (mlexpr_of_expr mlenv rg lenv e)
in (_70_26735)::[])
end)) args)
in (match (sube) with
| ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) | ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)
end
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, _69_902)); Microsoft_FStar_Absyn_Syntax.tk = _69_899; Microsoft_FStar_Absyn_Syntax.pos = _69_897; Microsoft_FStar_Absyn_Syntax.fvs = _69_895; Microsoft_FStar_Absyn_Syntax.uvs = _69_893} -> begin
(let subns = (let _70_26737 = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (Support.String.concat "." _70_26737))
in (let _69_914 = (match ((Support.List.rev c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)) with
| [] -> begin
("", [])
end
| h::t -> begin
(h.Microsoft_FStar_Absyn_Syntax.idText, (Support.List.rev t))
end)
in (match (_69_914) with
| (rn, subnsl) -> begin
(match ((let _70_26738 = (Support.Microsoft.FStar.Util.smap_try_find record_constructors subns)
in (_70_26738, args))) with
| (Some (_69_916), arg::[]) -> begin
(let _70_26741 = (let _70_26740 = (let _70_26739 = (path_of_ns mlenv subnsl)
in (_70_26739, c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (arg, _70_26740))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Proj (_70_26741))
end
| (Some (_69_922), arg::args) -> begin
(let _70_26746 = (let _70_26745 = (let _70_26744 = (let _70_26743 = (let _70_26742 = (path_of_ns mlenv subnsl)
in (_70_26742, c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (arg, _70_26743))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Proj (_70_26744))
in (_70_26745, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_70_26746))
end
| _69_929 -> begin
(let _70_26748 = (let _70_26747 = (mlexpr_of_expr mlenv rg lenv sube)
in (_70_26747, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_70_26748))
end)
end)))
end
| _69_931 -> begin
(let _70_26750 = (let _70_26749 = (mlexpr_of_expr mlenv rg lenv sube)
in (_70_26749, args))
in Microsoft_FStar_Backends_ML_Syntax.MLE_App (_70_26750))
end))
end)
end)
end
| _69_933 -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _70_26751 = (lresolve lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Var (_70_26751))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))) -> begin
(mkCTor x.Microsoft_FStar_Absyn_Syntax.v [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _69_943)) -> begin
(let fid = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (match ((((Support.Microsoft.FStar.Util.starts_with fid "is_") && ((Support.String.length fid) > 3)) && (let _70_26752 = (Support.Microsoft.FStar.Util.char_at fid 3)
in (Support.Microsoft.FStar.Util.is_upper _70_26752)))) with
| true -> begin
(let sub = (Support.Microsoft.FStar.Util.substring_from fid 3)
in (let mlid = (fresh "_discr_")
in (let rid = (let _69_949 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ns = _69_949.Microsoft_FStar_Absyn_Syntax.ns; Microsoft_FStar_Absyn_Syntax.ident = (let _69_951 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = sub; Microsoft_FStar_Absyn_Syntax.idRange = _69_951.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = _69_949.Microsoft_FStar_Absyn_Syntax.nsstr; Microsoft_FStar_Absyn_Syntax.str = sub})
in (let _70_26760 = (let _70_26759 = (let _70_26758 = (let _70_26757 = (let _70_26756 = (let _70_26755 = (let _70_26754 = (let _70_26753 = (mlpath_of_lident mlenv rid)
in (_70_26753, (Microsoft_FStar_Backends_ML_Syntax.MLP_Wild)::[]))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_70_26754))
in (_70_26755, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (true))))
in (_70_26756)::((Microsoft_FStar_Backends_ML_Syntax.MLP_Wild, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Const (Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (false))))::[])
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_ML_Syntax.idsym mlid))), _70_26757))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match (_70_26758))
in (((mlid, None))::[], _70_26759))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun (_70_26760)))))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr)) with
| Some ((_69_955, projs)) -> begin
(let mlid = (fresh "_proj_")
in (let cargs = (Support.List.map (fun ( x ) -> (let _70_26762 = (fresh x)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Var (_70_26762))) projs)
in (let _69_964 = (Support.List.rev x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_69_964) with
| cn::cr -> begin
(let crstr = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) cr)
in (let rid = {Microsoft_FStar_Absyn_Syntax.ns = cr; Microsoft_FStar_Absyn_Syntax.ident = (let _69_967 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = cn.Microsoft_FStar_Absyn_Syntax.idText; Microsoft_FStar_Absyn_Syntax.idRange = _69_967.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = (Support.String.concat "." crstr); Microsoft_FStar_Absyn_Syntax.str = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr}
in (let cn = cn.Microsoft_FStar_Absyn_Syntax.idText
in (let _70_26771 = (let _70_26770 = (let _70_26769 = (let _70_26768 = (let _70_26767 = (let _70_26766 = (let _70_26765 = (let _70_26764 = (mlpath_of_lident mlenv rid)
in (_70_26764, cargs))
in Microsoft_FStar_Backends_ML_Syntax.MLP_CTor (_70_26765))
in (_70_26766, None, Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))))
in (_70_26767)::[])
in (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_ML_Syntax.idsym mlid))), _70_26768))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match (_70_26769))
in (((mlid, None))::[], _70_26770))
in Microsoft_FStar_Backends_ML_Syntax.MLE_Fun (_70_26771)))))
end))))
end
| None -> begin
(let _70_26772 = (mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Name (_70_26772))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _70_26773 = (mlconst_of_const c)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Const (_70_26773))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (([], e)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inl (_69_980), _69_983)::rest, e)) -> begin
(let _70_26774 = (match ((Support.List.isEmpty rest)) with
| true -> begin
e
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlexpr_of_expr mlenv rg lenv _70_26774))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inr (x), _69_993)::rest, e)) -> begin
(let _69_1001 = (lpush lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_69_1001) with
| (lenv, mlid) -> begin
(let e = (let _70_26775 = (match ((Support.List.isEmpty rest)) with
| true -> begin
e
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (mlexpr_of_expr mlenv rg lenv _70_26775))
in (Microsoft_FStar_Backends_ML_Syntax.mlfun mlid e))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((x, (p, None, e)::[])) when (Microsoft_FStar_Absyn_Util.is_wild_pat p) -> begin
(match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_69_1012) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_69_1015) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| _69_1018 -> begin
(Support.All.failwith "Impossible")
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
| _69_1071 -> begin
(let e = (mlexpr_of_expr mlenv rg lenv e)
in (let bs = (Support.List.map (mlbranch_of_branch mlenv rg lenv) bs)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((e, bs))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((rec_, lb), body)) -> begin
(let _69_1082 = (mllets_of_lets mlenv rg lenv (rec_, lb))
in (match (_69_1082) with
| (lenv, bindings) -> begin
(let body = (mlexpr_of_expr mlenv rg lenv body)
in Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, bindings), body)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let _69_1089 = ()
in (let _69_1129 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) | (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_)))); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args))) -> begin
(c, args)
end
| _69_1126 -> begin
(unexpected rg "meta-data-app-without-fvar")
end)
in (match (_69_1129) with
| (c, args) -> begin
(let args = (Support.All.pipe_right args (Support.List.collect (fun ( _69_13 ) -> (match (_69_13) with
| (Support.Microsoft.FStar.Util.Inr (e), _69_1134) -> begin
(e)::[]
end
| _69_1137 -> begin
[]
end))))
in (let args = (Support.List.map (mlexpr_of_expr mlenv rg lenv) args)
in (mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_69_1152); Microsoft_FStar_Absyn_Syntax.lbtyp = _69_1150; Microsoft_FStar_Absyn_Syntax.lbeff = _69_1148; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let d1 = (mlexpr_of_expr mlenv rg lenv e1)
in (let d2 = (mlexpr_of_expr mlenv rg lenv e2)
in (Microsoft_FStar_Backends_ML_Syntax.mlseq d1 d2)))
end
| _69_1163 -> begin
(unexpected rg "expr-seq-mark-without-let")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Primop))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _69_1171, _69_1173)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.MaskedEffect))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_69_1182) -> begin
(unexpected rg "expr-app")
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_69_1185) -> begin
(unexpected rg "expr-uvar")
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_69_1188) -> begin
(unexpected rg "expr-delayed")
end)
end))))))
and mllets_of_lets = (fun ( mlenv ) ( rg ) ( lenv ) ( _69_1195 ) -> (match (_69_1195) with
| (rec_, lbs) -> begin
(let downct = (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(x, lb.Microsoft_FStar_Absyn_Syntax.lbdef)
end
| Support.Microsoft.FStar.Util.Inr (_69_1201) -> begin
(unexpected rg "expr-let-in-with-fvar")
end))
in (let lbs = (Support.List.map downct lbs)
in (let _69_1211 = (Support.Microsoft.FStar.Util.fold_map (fun ( lenv ) ( _69_1208 ) -> (match (_69_1208) with
| (x, _69_1207) -> begin
(lpush lenv x.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.ppname)
end)) lenv lbs)
in (match (_69_1211) with
| (lenvb, mlids) -> begin
(let es = (let inlenv = (match (rec_) with
| true -> begin
lenvb
end
| false -> begin
lenv
end)
in (Support.List.map (fun ( _69_1215 ) -> (match (_69_1215) with
| (x, e) -> begin
(let mlid = (lresolve lenvb x.Microsoft_FStar_Absyn_Syntax.realname)
in (let _70_26786 = (mlexpr_of_expr mlenv rg inlenv e)
in (mlid, None, [], _70_26786)))
end)) lbs))
in (lenvb, es))
end))))
end))
and mlbranch_of_branch = (fun ( mlenv ) ( rg ) ( lenv ) ( _69_1224 ) -> (match (_69_1224) with
| (pat, when_, body) -> begin
(let _69_1227 = (mlpat_of_pat mlenv rg lenv pat)
in (match (_69_1227) with
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

let mldtype_of_indt = (fun ( mlenv ) ( indt ) -> (let rec getRecordFieldsFromType = (fun ( _69_14 ) -> (match (_69_14) with
| [] -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.RecordType (f)::_69_1250 -> begin
(let _70_26829 = (Support.All.pipe_right f (Support.List.map (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.ident)))
in Some (_70_26829))
end
| _69_1257::qualif -> begin
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
(let _70_26836 = (Support.All.pipe_right bs (Support.List.collect (fun ( _69_15 ) -> (match (_69_15) with
| (Support.Microsoft.FStar.Util.Inr (x), _69_1275) -> begin
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
| _69_1280 -> begin
[]
end))))
in (let _70_26835 = (comp_vars c.Microsoft_FStar_Absyn_Syntax.n)
in (Support.List.append _70_26836 _70_26835)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t))) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) -> begin
(type_vars t.Microsoft_FStar_Absyn_Syntax.n)
end
| _69_1314 -> begin
[]
end))
in (let _69_1388 = (let fold1 = (fun ( sigelt ) ( _69_1319 ) -> (match (_69_1319) with
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
in (let ty = (match ((let _70_26841 = (getRecordFieldsFromType qualif)
in (_70_26841, cs))) with
| (Some (f), c::[]) -> begin
(let _69_1338 = (Support.Microsoft.FStar.Util.smap_add record_constructors c.Microsoft_FStar_Absyn_Syntax.str f)
in (let _70_26844 = (let _70_26843 = (let _70_26842 = (tenv_of_tvmap ar)
in (Support.Prims.snd _70_26842))
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, f, cs, _70_26843, rg))
in Rec (_70_26844)))
end
| (_69_1341, _69_1343) -> begin
(let _70_26847 = (let _70_26846 = (let _70_26845 = (tenv_of_tvmap ar)
in (Support.Prims.snd _70_26845))
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, cs, _70_26846, rg))
in DT (_70_26847))
end)
in ((ty)::types, ctors)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, pr, _69_1350, _69_1352, rg)) -> begin
(let actr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let anames = (let _70_26851 = (type_vars ty.Microsoft_FStar_Absyn_Syntax.n)
in (Support.List.map (fun ( _69_16 ) -> (match (_69_16) with
| None -> begin
(let _69_1359 = (Support.Microsoft.FStar.Util.incr actr)
in (let _70_26850 = (let _70_26849 = (Support.ST.read actr)
in (Support.Microsoft.FStar.Util.string_of_int _70_26849))
in (Support.String.strcat "_" _70_26850)))
end
| Some (x) -> begin
(let _69_1363 = (Support.Microsoft.FStar.Util.incr actr)
in x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end)) _70_26851))
in (let _69_1366 = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.str ((Support.List.length anames), anames))
in (types, ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (ty, pr)))::ctors))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((x, tps, k, body, _69_1373, rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _70_26855 = (let _70_26854 = (let _70_26853 = (let _70_26852 = (tenv_of_tvmap ar)
in (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, body, _70_26852, rg))
in Abb (_70_26853))
in (_70_26854)::types)
in (_70_26855, ctors)))
end
| _69_1382 -> begin
(unexpected (Microsoft_FStar_Absyn_Util.range_of_sigelt sigelt) "no-dtype-or-abbrvs-in-bundle")
end)
end))
in (let _69_1385 = (Support.List.fold_right fold1 indt ([], []))
in (match (_69_1385) with
| (ts, cs) -> begin
(let _70_26856 = (Support.Microsoft.FStar.Util.smap_of_list cs)
in (ts, _70_26856))
end)))
in (match (_69_1388) with
| (ts, cs) -> begin
(let cons_args = (fun ( cname ) ( tparams ) ( rg ) ( x ) -> (let _69_1397 = (let _70_26865 = (Support.Microsoft.FStar.Util.smap_try_find cs cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.All.pipe_right _70_26865 Support.Microsoft.FStar.Util.must))
in (match (_69_1397) with
| (c, _69_1396) -> begin
(let _69_1401 = (strip_polymorphism [] rg c)
in (match (_69_1401) with
| (cparams, rgty, c) -> begin
(let _69_1402 = (match (((Support.List.length cparams) <> (Support.List.length tparams))) with
| true -> begin
(unexpected rg "invalid-number-of-ctor-params")
end
| false -> begin
()
end)
in (let cparams = (Support.List.map (fun ( _69_1407 ) -> (match (_69_1407) with
| (x, _69_1406) -> begin
x.Microsoft_FStar_Absyn_Syntax.idText
end)) cparams)
in (let tenv = (Support.List.zip cparams tparams)
in (let tenv = (let _70_26867 = (Support.Microsoft.FStar.Util.smap_of_list tenv)
in TEnv (_70_26867))
in (let c = (mlty_of_ty mlenv tenv (rgty, c))
in (let _69_1414 = (mltycons_of_mlty c)
in (match (_69_1414) with
| (args, name) -> begin
(match (name) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((tyargs, name)) when ((Support.Prims.snd name) = x) -> begin
(let check = (fun ( x ) ( mty ) -> (match (mty) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (mtyx) -> begin
(x = mtyx)
end
| _69_1425 -> begin
false
end))
in (let _69_1426 = (match (((Support.List.length tyargs) <> (Support.List.length cparams))) with
| true -> begin
(unexpected rg "dtype-invalid-ctor-result")
end
| false -> begin
()
end)
in (let _69_1428 = (match ((not ((Support.List.forall2 check tparams tyargs)))) with
| true -> begin
(unsupported rg "dtype-invalid-ctor-result")
end
| false -> begin
()
end)
in args)))
end
| _69_1431 -> begin
(unexpected rg "dtype-invalid-ctor-result")
end)
end)))))))
end))
end)))
in (let fortype = (fun ( ty ) -> (match (ty) with
| DT ((x, tcs, tparams, rg)) -> begin
(let mldcons_of_cons = (fun ( cname ) -> (let args = (cons_args cname tparams rg x)
in (cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))
in (let _70_26877 = (let _70_26876 = (Support.List.map mldcons_of_cons tcs)
in Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (_70_26876))
in (x, tparams, _70_26877)))
end
| Rec ((x, f, tcs, tparams, rg)) -> begin
(let args = (match (tcs) with
| cname::[] -> begin
(cons_args cname tparams rg x)
end
| _69_1453 -> begin
(unexpected rg "records-should-have-one-single-constructor")
end)
in (let mldproj_of_proj = (fun ( name ) ( c ) -> (name.Microsoft_FStar_Absyn_Syntax.idText, c))
in (let _69_1459 = (match (((Support.List.length f) <> (Support.List.length args))) with
| true -> begin
(let _70_26888 = (let _70_26887 = (let _70_26882 = (Support.List.hd tcs)
in _70_26882.Microsoft_FStar_Absyn_Syntax.str)
in (let _70_26886 = (let _70_26884 = (Support.List.map (fun ( f ) -> f.Microsoft_FStar_Absyn_Syntax.idText) f)
in (Support.All.pipe_right _70_26884 (Support.String.concat ", ")))
in (let _70_26885 = (Support.All.pipe_right (Support.List.length args) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format4 "%s, %s, %s fields, %s args" x _70_26887 _70_26886 _70_26885))))
in (unexpected rg _70_26888))
end
| false -> begin
()
end)
in (let _70_26890 = (let _70_26889 = (Support.List.map2 mldproj_of_proj f args)
in Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (_70_26889))
in (x, tparams, _70_26890)))))
end
| Abb ((x, body, (tenv, tparams), rg)) -> begin
(let body = (mlty_of_ty mlenv tenv (rg, body))
in (x, tparams, Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (body)))
end))
in (Support.List.map fortype ts)))
end)))))

let mlmod1_of_mod1 = (fun ( mode ) ( mlenv ) ( modx ) -> (let export_val = (fun ( qal ) -> (let export_val1 = (fun ( _69_17 ) -> (match (_69_17) with
| (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) | (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Private) -> begin
false
end
| _69_1485 -> begin
true
end))
in (Support.List.for_all export_val1 qal)))
in (match (modx) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma (_69_1488) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when ((export_val qal) && (mode = Sig)) -> begin
(let _69_1498 = (mlscheme_of_ty mlenv rg ty)
in (match (_69_1498) with
| (tparams, ty) -> begin
Some (Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (tparams, ty)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when (mode = Sig) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((rec_, lbs), rg, _69_1510, _69_1512)) when (mode = Struct) -> begin
(let downct = (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(x, lb.Microsoft_FStar_Absyn_Syntax.lbdef)
end
| Support.Microsoft.FStar.Util.Inl (_69_1520) -> begin
(unexpected rg "expr-top-let-with-bvar")
end))
in (let lbs = (Support.List.map downct lbs)
in (let lbs = (Support.List.map (fun ( _69_1525 ) -> (match (_69_1525) with
| (x, e) -> begin
(let _70_26904 = (mlexpr_of_expr mlenv rg (lenv_of_mlenv mlenv) e)
in ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (- (1))), None, [], _70_26904))
end)) lbs)
in Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lbs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, rg)) when (mode = Struct) -> begin
(let lenv = (lenv_of_mlenv mlenv)
in (let _70_26907 = (let _70_26906 = (let _70_26905 = (mlexpr_of_expr mlenv rg lenv e)
in Microsoft_FStar_Backends_ML_Syntax.MLM_Top (_70_26905))
in Support.Microsoft.FStar.Util.Inr (_70_26906))
in Some (_70_26907)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_69_1533, _69_1535, _69_1537, _69_1539, qal, _69_1542)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((t, tps, k, ty, _69_1550, rg)) -> begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let _69_1560 = (tenv_of_tvmap ar)
in (match (_69_1560) with
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
in (let _69_1578 = (tenv_of_tvmap ar)
in (match (_69_1578) with
| (_tenv, tparams) -> begin
Some ((mlitem1_ty mode (((t.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, tparams, None))::[])))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_69_1592, _69_1594, _69_1596, qal, _69_1599, _69_1601))::[], _69_1606, _69_1608, _69_1610)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, (tx, _69_1617, _69_1619), qal, _69_1623, rg))::[], _69_1629, _69_1631, _69_1633)) when ((as_tprims tx) = Some (Exn)) -> begin
(let rec aux = (fun ( acc ) ( ty ) -> (match ((let _70_26912 = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in _70_26912.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let tys = (Support.All.pipe_right bs (Support.List.collect (fun ( _69_18 ) -> (match (_69_18) with
| (Support.Microsoft.FStar.Util.Inl (_69_1645), _69_1648) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _69_1653) -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort)::[]
end))))
in tys)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (x) when ((as_tprims x.Microsoft_FStar_Absyn_Syntax.v) = Some (Exn)) -> begin
(Support.List.rev acc)
end
| _69_1659 -> begin
(unexpected rg "invalid-exn-type")
end))
in (let args = (aux [] ty)
in (let tenv = (let _70_26914 = (tenv_of_tvmap [])
in (Support.Prims.fst _70_26914))
in (let args = (Support.List.map (fun ( ty ) -> (mlty_of_ty mlenv tenv (rg, ty))) args)
in Some ((mlitem1_exn mode (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((indt, _69_1666, _69_1668, _69_1670)) -> begin
(let aout = (mldtype_of_indt mlenv indt)
in (let aout = (Support.List.map (fun ( _69_1677 ) -> (match (_69_1677) with
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
| Microsoft_FStar_Absyn_Syntax.Sig_assume (_69_1682) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_69_1685) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_69_1688) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_69_1691) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_69_1694) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (_69_1697) -> begin
None
end)))

let mlmod_of_mod = (fun ( mlenv ) ( modx ) -> (let asright = (fun ( _69_19 ) -> (match (_69_19) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inl (_69_1705) -> begin
(Support.All.failwith "asright")
end))
in (Support.List.choose (fun ( x ) -> (let _70_26924 = (mlmod1_of_mod1 Struct mlenv x)
in (Support.Option.map asright _70_26924))) modx)))

let mlsig_of_sig = (fun ( mlenv ) ( modx ) -> (let asleft = (fun ( _69_20 ) -> (match (_69_20) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inr (_69_1715) -> begin
(Support.All.failwith "asleft")
end))
in (Support.List.choose (fun ( x ) -> (let _70_26932 = (mlmod1_of_mod1 Sig mlenv x)
in (Support.Option.map asleft _70_26932))) modx)))

let mlmod_of_fstar = (fun ( fmod_ ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _69_1721 = (Support.Microsoft.FStar.Util.fprint1 "OCaml extractor : %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let mod_ = (mlmod_of_mod (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (let sig_ = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (name, sig_, mod_))))))

let mlmod_of_iface = (fun ( fmod_ ) -> (let name = (Microsoft_FStar_Backends_ML_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _69_1727 = (Support.Microsoft.FStar.Util.fprint1 "OCaml skip: %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let _70_26937 = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.All.pipe_right _70_26937 Support.Prims.ignore)))))

let mllib_empty = Microsoft_FStar_Backends_ML_Syntax.MLLib ([])

let rec mllib_add = (fun ( _69_1730 ) ( _69_1734 ) -> (match ((_69_1730, _69_1734)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib), (path, sig_, mod_)) -> begin
(let n = (Support.String.concat "_" (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[])))
in (let rec aux = (fun ( _69_21 ) -> (match (_69_21) with
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
(let _70_26944 = (aux tl)
in (the)::_70_26944)
end))
end
| (name, Some ((ssig, mmod)), sublibs)::tl -> begin
(let the = (name, Some ((ssig, mmod)), sublibs)
in (match ((name = (Support.Prims.snd path))) with
| true -> begin
((name, Some ((ssig, mod_)), sublibs))::tl
end
| false -> begin
(let _70_26945 = (aux tl)
in (the)::_70_26945)
end))
end))
in (let _70_26946 = (aux mllib)
in Microsoft_FStar_Backends_ML_Syntax.MLLib (_70_26946))))
end))

let mlmod_of_fstars = (fun ( fmods ) -> (let in_std_ns = (fun ( x ) -> (let _70_26952 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.Microsoft.FStar.Util.for_some (fun ( y ) -> (in_ns (y, x))) _70_26952)))
in (let fmods = (Support.List.filter (fun ( x ) -> (let _69_1761 = (Support.Microsoft.FStar.Util.fprint1 "Extract module: %s\n" x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (not ((let _70_26955 = (Support.List.map (fun ( y ) -> y.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ns)
in (in_std_ns _70_26955)))))) fmods)
in (let stdlib = (Support.List.map (fun ( x ) -> (Support.Microsoft.FStar.Util.concat_l "." x)) outmod)
in (let extlib = (let _70_26958 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.map (fun ( x ) -> (Support.Microsoft.FStar.Util.concat_l "." x)) _70_26958))
in (let fmods = (Support.List.filter (fun ( x ) -> (not ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str stdlib)))) fmods)
in (let fmods = (Support.List.choose (fun ( x ) -> (match ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str extlib)) with
| true -> begin
(let _69_1772 = (mlmod_of_iface x)
in None)
end
| false -> begin
(let _70_26961 = (mlmod_of_fstar x)
in Some (_70_26961))
end)) fmods)
in (let for1 = (fun ( mllib ) ( the ) -> (let _69_1781 = the
in (match (_69_1781) with
| (path, sig_, mod_) -> begin
(let modname = (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[]))
in (let rec checkname = (fun ( modname ) ( fbd ) -> (match ((modname, fbd)) with
| (_69_1787, []) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(checkname t1 t2)
end
| _69_1798 -> begin
false
end))
in (let aout = (mllib_add mllib the)
in aout)))
end)))
in (Support.List.fold_left for1 mllib_empty fmods)))))))))




