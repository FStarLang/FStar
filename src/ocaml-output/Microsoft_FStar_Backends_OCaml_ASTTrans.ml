
type mlenv =
{mle_name : Microsoft_FStar_Backends_OCaml_Syntax.mlpath}

let mk_mlenv = (fun name -> {mle_name = name})

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Set")::[])::(("Map")::[])::(("Heap")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let record_constructors = (Support.Microsoft.FStar.Util.smap_create 17)

let algebraic_constructors = (Support.Microsoft.FStar.Util.smap_create 40)

let _ign = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors "Prims.Some" (1, ("v")::[]))

let rec in_ns = (fun _52_1 -> (match (_52_1) with
| ([], _) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_, _) -> begin
false
end))

let path_of_ns = (fun mlenv ns -> (let ns = (Support.List.map (fun x -> x.Microsoft_FStar_Absyn_Syntax.idText) ns)
in (let outsupport = (fun _52_48 -> (match (_52_48) with
| (ns1, ns2) -> begin
if (ns1 = ns2) then begin
[]
end else begin
((Support.String.concat "_" ns2))::[]
end
end))
in (let chkin = (fun sns -> if (in_ns (sns, ns)) then begin
Some (sns)
end else begin
None
end)
in (match ((Support.List.tryPick chkin outmod)) with
| None -> begin
(match ((Support.List.tryPick chkin (! (Microsoft_FStar_Options.codegen_libs)))) with
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

let mlpath_of_lident = (fun mlenv x -> (match (x.Microsoft_FStar_Absyn_Syntax.str) with
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
in ((path_of_ns mlenv ns), x)))
end))

type error =
| Unexpected of string
| Unsupported of string
| UnboundVar of string
| UnboundTyVar of string
| DuplicatedLocal of (string * string)

exception OCamlFailure of ((Support.Microsoft.FStar.Range.range * error))

let string_of_error = (fun error -> (match (error) with
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

let unexpected = (fun rg what -> (raise (OCamlFailure ((rg, Unexpected (what))))))

let unsupported = (fun rg what -> (raise (OCamlFailure ((rg, Unsupported (what))))))

let unbound_var = (fun rg x -> (raise (OCamlFailure ((rg, UnboundVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let unbound_ty_var = (fun rg x -> (raise (OCamlFailure ((rg, UnboundTyVar (x.Microsoft_FStar_Absyn_Syntax.idText))))))

let duplicated_local = (fun rg x -> (raise (OCamlFailure ((rg, DuplicatedLocal (x))))))

let fresh = (let c = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun x -> (let _52_105 = (Support.Microsoft.FStar.Util.incr c)
in (x, (! (c))))))

let tyvar_of_int = (let tyvars = "abcdefghijklmnopqrstuvwxyz"
in (let rec aux = (fun n -> (let s = (Support.Microsoft.FStar.Util.string_of_char (Support.String.get tyvars (n mod 26)))
in if (n >= (Support.String.length tyvars)) then begin
(Support.String.strcat (aux (n / 26)) s)
end else begin
s
end))
in (fun n -> (Support.String.strcat "\'" (aux n)))))

type lenv =
| LEnv of Microsoft_FStar_Backends_OCaml_Syntax.mlident Support.Microsoft.FStar.Util.smap

let lempty = LEnv ((Support.Microsoft.FStar.Util.smap_create 0))

let lenv_of_mlenv = (fun _52_113 -> lempty)

let lpush = (fun _52_116 real pp -> (match (_52_116) with
| LEnv (lenv) -> begin
(let mlid = (fresh pp.Microsoft_FStar_Absyn_Syntax.idText)
in (let _52_120 = (Support.Microsoft.FStar.Util.smap_add lenv real.Microsoft_FStar_Absyn_Syntax.idText mlid)
in (LEnv (lenv), mlid)))
end))

let lresolve = (fun _52_123 x -> (match (_52_123) with
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
| TEnv of Microsoft_FStar_Backends_OCaml_Syntax.mlident Support.Microsoft.FStar.Util.smap

let tempty = TEnv ((Support.Microsoft.FStar.Util.smap_create 0))

let tvsym = (fun _52_131 -> (match (_52_131) with
| (x, n) -> begin
if (Support.Microsoft.FStar.Util.starts_with x "\'") then begin
(x, n)
end else begin
((Support.String.strcat "\'" x), n)
end
end))

let tenv_of_tvmap = (fun tvs -> (let rec fresh_tyvar = (fun used i -> (let pp = (tyvar_of_int 0)
in if (Support.Microsoft.FStar.Util.set_mem pp used) then begin
(fresh_tyvar used (i + 1))
end else begin
((Support.Microsoft.FStar.Util.set_add pp used), pp)
end))
in (let freshen = (fun used pp -> (match (pp) with
| Some (pp) when (not ((Support.Microsoft.FStar.Util.set_mem pp.Microsoft_FStar_Absyn_Syntax.idText used))) -> begin
((Support.Microsoft.FStar.Util.set_add pp.Microsoft_FStar_Absyn_Syntax.idText used), pp.Microsoft_FStar_Absyn_Syntax.idText)
end
| _ -> begin
(fresh_tyvar used 0)
end))
in (let _52_164 = (let for1 = (fun used tv -> (match (tv) with
| Some ((real, pp)) -> begin
(let _52_153 = (freshen used (Some (pp)))
in (match (_52_153) with
| (used, pp) -> begin
(used, ((fresh pp), Some (real.Microsoft_FStar_Absyn_Syntax.idText)))
end))
end
| None -> begin
(let _52_157 = (freshen used None)
in (match (_52_157) with
| (used, pp) -> begin
(used, ((fresh pp), None))
end))
end))
in (Support.Microsoft.FStar.Util.fold_map for1 (Support.Microsoft.FStar.Util.new_set (fun x y -> if (x = y) then begin
0
end else begin
1
end) (fun x -> 0)) tvs))
in (match (_52_164) with
| (_, tvs) -> begin
(let tparams = (Support.List.map (fun _52_168 -> (match (_52_168) with
| (x, _) -> begin
(tvsym x)
end)) tvs)
in (let tvs = (Support.List.choose (fun _52_172 -> (match (_52_172) with
| (x, y) -> begin
(match (y) with
| None -> begin
None
end
| Some (y) -> begin
Some ((y, (tvsym x)))
end)
end)) tvs)
in (TEnv ((Support.Microsoft.FStar.Util.smap_of_list tvs)), tparams)))
end)))))

let tvar_of_btvar = (fun _52_178 x -> (match (_52_178) with
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

let is_prim_ns = (fun ns -> (match (ns) with
| {Microsoft_FStar_Absyn_Syntax.idText = "Prims"; Microsoft_FStar_Absyn_Syntax.idRange = _}::[] -> begin
true
end
| _ -> begin
false
end))

type tprims =
| Tuple of int
| Exn

let as_tprims = (fun id -> if (is_prim_ns id.Microsoft_FStar_Absyn_Syntax.ns) then begin
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
end else begin
None
end)

let is_xtuple = (fun x -> if (is_prim_ns x.Microsoft_FStar_Absyn_Syntax.ns) then begin
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
end else begin
None
end)

let is_etuple = (fun e -> (match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(let args = (Support.List.collect (fun _52_2 -> (match (_52_2) with
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

let is_ptuple = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, args)) -> begin
(let args = ((Support.List.collect (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end
| _ -> begin
(p)::[]
end))) args)
in (match ((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
if (k = (Support.List.length args)) then begin
Some (k)
end else begin
None
end
end
| _ -> begin
None
end))
end
| _ -> begin
None
end))

let mlconst_of_const = (fun rg sctt -> (match (sctt) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Unit
end
| Microsoft_FStar_Absyn_Syntax.Const_char (c) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Char (c)
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (c) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Byte (c)
end
| Microsoft_FStar_Absyn_Syntax.Const_int (c) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Int32 ((Support.Microsoft.FStar.Util.int32_of_int (Support.Microsoft.FStar.Util.int_of_string c)))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Int32 (i)
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (i) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Int64 (i)
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bool (b)
end
| Microsoft_FStar_Absyn_Syntax.Const_float (d) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Float (d)
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((bytes, _)) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bytes (bytes)
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLC_String ((Support.Microsoft.FStar.Util.string_of_unicode bytes))
end))

let mlkind_of_kind = (fun tps k -> (let mltparam_of_tparam = (fun _52_3 -> (match (_52_3) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}; Microsoft_FStar_Absyn_Syntax.p = _}), _) -> begin
Some ((x.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.ppname))
end
| x -> begin
None
end))
in (let rec aux = (fun acc k -> (match ((Microsoft_FStar_Absyn_Util.compress_kind k).Microsoft_FStar_Absyn_Syntax.n) with
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
(let x = if (Microsoft_FStar_Absyn_Syntax.is_null_binder (Support.Microsoft.FStar.Util.Inl (x), None)) then begin
None
end else begin
Some ((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))
end
in (aux ((x)::acc) (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (rest, k2) k.Microsoft_FStar_Absyn_Syntax.pos)))
end
| _ -> begin
None
end)
end
| _ -> begin
None
end))
in (let aout = (Support.List.choose mltparam_of_tparam tps)
in (let some = (fun x -> Some (x))
in (aux (Support.List.rev (Support.List.map some aout)) k))))))

let rec mlty_of_ty_core = (fun mlenv tenv _52_366 -> (match (_52_366) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let ty = (Microsoft_FStar_Absyn_Util.compress_typ ty)
in (match (ty.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (x) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Var ((tvar_of_btvar tenv x))
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
in Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Fun ((mlt1, mlt2)))))
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
in Microsoft_FStar_Backends_OCaml_Syntax.MLTY_App ((mlt1, mlt2)))))
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
and maybe_named = (fun mlenv tenv _52_480 -> (match (_52_480) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec aux = (fun acc _52_486 -> (match (_52_486) with
| (rg, ty) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_typ ty).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
Some (((mlpath_of_lident mlenv c.Microsoft_FStar_Absyn_Syntax.v), acc))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _52_4 -> (match (_52_4) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| _ -> begin
false
end))) args) then begin
None
end else begin
(let tys = ((Support.List.map (fun _52_5 -> (match (_52_5) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(mlty_of_ty mlenv tenv (rg, t))
end
| _ -> begin
(failwith "impos")
end))) args)
in (aux (Support.List.append tys acc) (rg, head)))
end
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
and maybe_tuple = (fun mlenv tenv _52_532 -> (match (_52_532) with
| (rg, ty) -> begin
(let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (let rec unfun = (fun n ty -> if (n <= 0) then begin
Some (ty)
end else begin
(match ((Microsoft_FStar_Absyn_Util.compress_typ ty).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, ty)) -> begin
(unfun (n - (Support.List.length bs)) ty)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(unfun n ty)
end
| _ -> begin
None
end)
end)
in (let rec aux = (fun acc ty -> (match ((Microsoft_FStar_Absyn_Util.compress_typ ty).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (c) -> begin
(match ((as_tprims c.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (Tuple (n)) -> begin
if ((Support.List.length acc) <> n) then begin
None
end else begin
Some ((Support.List.map (fun ty -> (mlty_of_ty mlenv tenv (rg, ty))) acc))
end
end
| _ -> begin
None
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _52_6 -> (match (_52_6) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
false
end))) args) then begin
None
end else begin
(let tys = ((Support.List.map (fun _52_7 -> (match (_52_7) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
t
end
| _ -> begin
(failwith "impos")
end))) args)
in (aux (Support.List.append tys acc) head))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((ty, _)) -> begin
(aux acc ty)
end
| _ -> begin
None
end))
in (aux [] ty))))
end))
and mlty_of_ty = (fun mlenv tenv rgty -> (match ((maybe_tuple mlenv tenv rgty)) with
| Some (x) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Tuple (x)
end
| None -> begin
(match ((maybe_named mlenv tenv rgty)) with
| Some (x) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Named (((Support.Prims.snd x), (Support.Prims.fst x)))
end
| None -> begin
(mlty_of_ty_core mlenv tenv rgty)
end)
end))

let mltycons_of_mlty = (fun ty -> (let rec aux = (fun acc ty -> (match (ty) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Fun ((dom, codom)) -> begin
(aux ((dom)::acc) codom)
end
| _ -> begin
((Support.List.rev acc), ty)
end))
in (aux [] ty)))

let rec strip_polymorphism = (fun acc rg ty -> (let rg = ty.Microsoft_FStar_Absyn_Syntax.pos
in (match ((Microsoft_FStar_Absyn_Util.compress_typ ty).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _52_641 = ((Support.List.partition (fun _52_8 -> (match (_52_8) with
| (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}; Microsoft_FStar_Absyn_Syntax.p = _}), _) -> begin
true
end
| _ -> begin
false
end))) bs)
in (match (_52_641) with
| (ts, vs) -> begin
(let ts = ((Support.List.collect (fun _52_9 -> (match (_52_9) with
| (Support.Microsoft.FStar.Util.Inl (x), _) -> begin
((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname, x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname))::[]
end
| _ -> begin
[]
end))) ts)
in (match ((vs, c.Microsoft_FStar_Absyn_Syntax.n)) with
| ([], Microsoft_FStar_Absyn_Syntax.Total (ty)) -> begin
(ts, rg, ty)
end
| ([], Microsoft_FStar_Absyn_Syntax.Comp (c)) -> begin
(ts, rg, c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| (_, _) -> begin
(ts, rg, (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (vs, c) None ty.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
end
| _ -> begin
((Support.List.rev acc), rg, ty)
end)))

let mlscheme_of_ty = (fun mlenv rg ty -> (let _52_672 = (strip_polymorphism [] rg ty)
in (match (_52_672) with
| (tparams, rg, ty) -> begin
(let some = (fun x -> Some (x))
in (let _52_677 = (tenv_of_tvmap (Support.List.map some tparams))
in (match (_52_677) with
| (tenv, tparams) -> begin
(tparams, (mlty_of_ty mlenv tenv (rg, ty)))
end)))
end)))

let rec mlpat_of_pat = (fun mlenv rg le p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((x, ps)) -> begin
(let ps = ((Support.List.filter (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
false
end
| _ -> begin
true
end))) ps)
in if ((is_xtuple x.Microsoft_FStar_Absyn_Syntax.v) = Some ((Support.List.length ps))) then begin
(let _52_700 = (Support.Microsoft.FStar.Util.fold_map (fun le pat -> (mlpat_of_pat mlenv pat.Microsoft_FStar_Absyn_Syntax.p le pat)) le ps)
in (match (_52_700) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_OCaml_Syntax.MLP_Tuple (ps))
end))
end else begin
(let _52_703 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_52_703) with
| (le, ps) -> begin
(let p = (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLP_Record (((path_of_ns mlenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns), (Support.List.zip (Support.List.map (fun x -> x.Microsoft_FStar_Absyn_Syntax.idText) f) ps)))
end
| None -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLP_CTor (((mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v), ps))
end)
in (le, p))
end))
end)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
(let _52_716 = (lpush le x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_52_716) with
| (le, mlid) -> begin
(le, Microsoft_FStar_Backends_OCaml_Syntax.MLP_Var (mlid))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(le, Microsoft_FStar_Backends_OCaml_Syntax.MLP_Const ((mlconst_of_const rg c)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _52_723 = (Support.Microsoft.FStar.Util.fold_map (mlpat_of_pat mlenv rg) le ps)
in (match (_52_723) with
| (le, ps) -> begin
(le, Microsoft_FStar_Backends_OCaml_Syntax.MLP_Branch (ps))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_) -> begin
(le, Microsoft_FStar_Backends_OCaml_Syntax.MLP_Wild)
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

let rec mlexpr_of_expr = (fun mlenv rg lenv e -> (let rg = e.Microsoft_FStar_Absyn_Syntax.pos
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let rec eta_expand_dataconst = (fun ct args nvars -> (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let rec bvs = (fun _52_10 -> (match (_52_10) with
| 0 -> begin
[]
end
| n -> begin
(let _52_754 = (Support.Microsoft.FStar.Util.incr ctr)
in (((Support.String.strcat "__dataconst_" (Support.Microsoft.FStar.Util.string_of_int (! (ctr)))), (! (ctr))))::(bvs (n - 1)))
end))
in (let vs = (bvs nvars)
in (let fapp = Microsoft_FStar_Backends_OCaml_Syntax.MLE_CTor ((ct, (Support.List.append args (Support.List.map (fun x -> Microsoft_FStar_Backends_OCaml_Syntax.MLE_Var (x)) vs))))
in Microsoft_FStar_Backends_OCaml_Syntax.MLE_Fun ((vs, fapp)))))))
in (let mkCTor = (fun c args -> (match ((Support.Microsoft.FStar.Util.smap_try_find record_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (f) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_Record (((path_of_ns mlenv c.Microsoft_FStar_Absyn_Syntax.ns), (Support.List.zip (Support.List.map (fun x -> x.Microsoft_FStar_Absyn_Syntax.idText) f) args)))
end
| None -> begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors c.Microsoft_FStar_Absyn_Syntax.str)) with
| Some ((n, _)) when (n > (Support.List.length args)) -> begin
(eta_expand_dataconst (mlpath_of_lident mlenv c) args (n - (Support.List.length args)))
end
| _ -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_CTor (((mlpath_of_lident mlenv c), args))
end)
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((sube, args)) -> begin
(match ((sube.Microsoft_FStar_Absyn_Syntax.n, args)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, false)), _::_::(Support.Microsoft.FStar.Util.Inr (a1), _)::a2::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_left") -> begin
(mlexpr_of_expr mlenv rg lenv (let _52_793 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a1, (a2)::[])); Microsoft_FStar_Absyn_Syntax.tk = _52_793.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _52_793.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _52_793.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _52_793.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, false)), _::_::a1::(Support.Microsoft.FStar.Util.Inr (a2), _)::[]) when (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "pipe_right") -> begin
(mlexpr_of_expr mlenv rg lenv (let _52_811 = e
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_app ((a2, (a1)::[])); Microsoft_FStar_Absyn_Syntax.tk = _52_811.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _52_811.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _52_811.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _52_811.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, false)), _) when ((((c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assume") || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.Assert")) || (c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str = "Prims.erase")) || (Support.Microsoft.FStar.Util.starts_with c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText "l__")) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_Const (Microsoft_FStar_Backends_OCaml_Syntax.MLC_Unit)
end
| (_, _) -> begin
(match ((is_etuple e)) with
| Some (k) -> begin
(let args = (Support.List.collect (fun _52_11 -> (match (_52_11) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
((mlexpr_of_expr mlenv rg lenv e))::[]
end)) args)
in Microsoft_FStar_Backends_OCaml_Syntax.MLE_Tuple (args))
end
| _ -> begin
(let args = (Support.List.collect (fun _52_12 -> (match (_52_12) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
((mlexpr_of_expr mlenv rg lenv e))::[]
end)) args)
in (match (sube) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, true)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)
end
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, false)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(let subns = (Support.String.concat "." (Support.List.map (fun x -> x.Microsoft_FStar_Absyn_Syntax.idText) c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns))
in (let _52_889 = (match ((Support.List.rev c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)) with
| [] -> begin
("", [])
end
| h::t -> begin
(h.Microsoft_FStar_Absyn_Syntax.idText, (Support.List.rev t))
end)
in (match (_52_889) with
| (rn, subnsl) -> begin
(match (((Support.Microsoft.FStar.Util.smap_try_find record_constructors subns), args)) with
| (Some (_), arg::[]) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_Proj ((arg, ((path_of_ns mlenv subnsl), c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
end
| (Some (_), arg::args) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_App ((Microsoft_FStar_Backends_OCaml_Syntax.MLE_Proj ((arg, ((path_of_ns mlenv subnsl), c.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))), args))
end
| _ -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_App (((mlexpr_of_expr mlenv rg lenv sube), args))
end)
end)))
end
| _ -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_App (((mlexpr_of_expr mlenv rg lenv sube), args))
end))
end)
end)
end
| _ -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_Var ((lresolve lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, false)) -> begin
(let fid = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in if (((Support.Microsoft.FStar.Util.starts_with fid "is_") && ((Support.String.length fid) > 3)) && (Support.Microsoft.FStar.Util.is_upper (Support.Microsoft.FStar.Util.char_at fid 3))) then begin
(let sub = (Support.Microsoft.FStar.Util.substring_from fid 3)
in (let mlid = (fresh "_discr_")
in (let rid = (let _52_918 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ns = _52_918.Microsoft_FStar_Absyn_Syntax.ns; Microsoft_FStar_Absyn_Syntax.ident = (let _52_920 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = sub; Microsoft_FStar_Absyn_Syntax.idRange = _52_920.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = _52_918.Microsoft_FStar_Absyn_Syntax.nsstr; Microsoft_FStar_Absyn_Syntax.str = sub})
in Microsoft_FStar_Backends_OCaml_Syntax.MLE_Fun (((mlid)::[], Microsoft_FStar_Backends_OCaml_Syntax.MLE_Match ((Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_OCaml_Syntax.idsym mlid))), ((Microsoft_FStar_Backends_OCaml_Syntax.MLP_CTor (((mlpath_of_lident mlenv rid), (Microsoft_FStar_Backends_OCaml_Syntax.MLP_Wild)::[])), None, Microsoft_FStar_Backends_OCaml_Syntax.MLE_Const (Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bool (true))))::((Microsoft_FStar_Backends_OCaml_Syntax.MLP_Wild, None, Microsoft_FStar_Backends_OCaml_Syntax.MLE_Const (Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bool (false))))::[])))))))
end else begin
(match ((Support.Microsoft.FStar.Util.smap_try_find algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr)) with
| Some ((_, projs)) -> begin
(let mlid = (fresh "_proj_")
in (let cargs = (Support.List.map (fun x -> Microsoft_FStar_Backends_OCaml_Syntax.MLP_Var ((fresh x))) projs)
in (let _52_933 = (Support.List.rev x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_52_933) with
| cn::cr -> begin
(let crstr = (Support.List.map (fun x -> x.Microsoft_FStar_Absyn_Syntax.idText) cr)
in (let rid = {Microsoft_FStar_Absyn_Syntax.ns = cr; Microsoft_FStar_Absyn_Syntax.ident = (let _52_936 = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident
in {Microsoft_FStar_Absyn_Syntax.idText = cn.Microsoft_FStar_Absyn_Syntax.idText; Microsoft_FStar_Absyn_Syntax.idRange = _52_936.Microsoft_FStar_Absyn_Syntax.idRange}); Microsoft_FStar_Absyn_Syntax.nsstr = (Support.String.concat "." crstr); Microsoft_FStar_Absyn_Syntax.str = x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.nsstr}
in (let cn = cn.Microsoft_FStar_Absyn_Syntax.idText
in Microsoft_FStar_Backends_OCaml_Syntax.MLE_Fun (((mlid)::[], Microsoft_FStar_Backends_OCaml_Syntax.MLE_Match ((Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name (([], (Microsoft_FStar_Backends_OCaml_Syntax.idsym mlid))), ((Microsoft_FStar_Backends_OCaml_Syntax.MLP_CTor (((mlpath_of_lident mlenv rid), cargs)), None, Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name (([], x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))))::[])))))))
end))))
end
| None -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name ((mlpath_of_lident mlenv x.Microsoft_FStar_Absyn_Syntax.v))
end)
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, true)) -> begin
(mkCTor x.Microsoft_FStar_Absyn_Syntax.v [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
Microsoft_FStar_Backends_OCaml_Syntax.MLE_Const ((mlconst_of_const rg c))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (([], e)) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inl (_), _)::rest, e)) -> begin
(mlexpr_of_expr mlenv rg lenv (if (Support.List.isEmpty rest) then begin
e
end else begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (((Support.Microsoft.FStar.Util.Inr (x), _)::rest, e)) -> begin
(let _52_974 = (lpush lenv x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)
in (match (_52_974) with
| (lenv, mlid) -> begin
(let e = (mlexpr_of_expr mlenv rg lenv (if (Support.List.isEmpty rest) then begin
e
end else begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, e) None e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (Microsoft_FStar_Backends_OCaml_Syntax.mlfun mlid e))
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
(failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, bs)) -> begin
(match (bs) with
| (({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e1)::({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e2)::[]) | (({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e1)::({Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true)); Microsoft_FStar_Absyn_Syntax.sort = _; Microsoft_FStar_Absyn_Syntax.p = _}, None, e2)::[]) -> begin
(let e = (mlexpr_of_expr mlenv rg lenv e)
in (let e1 = (mlexpr_of_expr mlenv rg lenv e1)
in (let e2 = (mlexpr_of_expr mlenv rg lenv e2)
in (Microsoft_FStar_Backends_OCaml_Syntax.mlif e (e1, e2)))))
end
| _ -> begin
(let e = (mlexpr_of_expr mlenv rg lenv e)
in (let bs = (Support.List.map (mlbranch_of_branch mlenv rg lenv) bs)
in Microsoft_FStar_Backends_OCaml_Syntax.MLE_Match ((e, bs))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((rec_, lb), body)) -> begin
(let _52_1055 = (mllets_of_lets mlenv rg lenv (rec_, lb))
in (match (_52_1055) with
| (lenv, bindings) -> begin
(let body = (mlexpr_of_expr mlenv rg lenv body)
in Microsoft_FStar_Backends_OCaml_Syntax.MLE_Let ((rec_, bindings, body)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Data_app))) -> begin
(let _52_1062 = (Support.Prims._assert ())
in (let _52_1084 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((c, true)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(c, args)
end
| _ -> begin
(unexpected rg "meta-data-app-without-fvar")
end)
in (match (_52_1084) with
| (c, args) -> begin
(let args = ((Support.List.collect (fun _52_13 -> (match (_52_13) with
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(e)::[]
end
| _ -> begin
[]
end))) args)
in (let args = (Support.List.map (mlexpr_of_expr mlenv rg lenv) args)
in (mkCTor c.Microsoft_FStar_Absyn_Syntax.v args)))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, (Support.Microsoft.FStar.Util.Inl (_), _, e1)::[]), e2)) -> begin
(let d1 = (mlexpr_of_expr mlenv rg lenv e1)
in (let d2 = (mlexpr_of_expr mlenv rg lenv e2)
in (Microsoft_FStar_Backends_OCaml_Syntax.mlseq d1 d2)))
end
| _ -> begin
(unexpected rg "expr-seq-mark-without-let")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Primop))) -> begin
(mlexpr_of_expr mlenv rg lenv e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _)) -> begin
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
and mllets_of_lets = (fun mlenv rg lenv _52_1146 -> (match (_52_1146) with
| (rec_, lbs) -> begin
(let downct = (fun _52_1152 -> (match (_52_1152) with
| (x, _, e) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(x, e)
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(unexpected rg "expr-let-in-with-fvar")
end)
end))
in (let lbs = (Support.List.map downct lbs)
in (let _52_1166 = (Support.Microsoft.FStar.Util.fold_map (fun lenv _52_1163 -> (match (_52_1163) with
| (x, _) -> begin
(lpush lenv x.Microsoft_FStar_Absyn_Syntax.realname x.Microsoft_FStar_Absyn_Syntax.ppname)
end)) lenv lbs)
in (match (_52_1166) with
| (lenvb, mlids) -> begin
(let es = (let inlenv = if rec_ then begin
lenvb
end else begin
lenv
end
in (Support.List.map (fun _52_1170 -> (match (_52_1170) with
| (x, e) -> begin
(let mlid = (lresolve lenvb x.Microsoft_FStar_Absyn_Syntax.realname)
in (mlid, [], (mlexpr_of_expr mlenv rg inlenv e)))
end)) lbs))
in (lenvb, es))
end))))
end))
and mlbranch_of_branch = (fun mlenv rg lenv _52_1179 -> (match (_52_1179) with
| (pat, when_, body) -> begin
(let _52_1182 = (mlpat_of_pat mlenv rg lenv pat)
in (match (_52_1182) with
| (lenv, pat) -> begin
(let when_ = (Support.Option.map (mlexpr_of_expr mlenv rg lenv) when_)
in (let body = (mlexpr_of_expr mlenv rg lenv body)
in (pat, when_, body)))
end))
end))

type mode =
| Sig
| Struct

type mlitem1 =
(Microsoft_FStar_Backends_OCaml_Syntax.mlsig1, Microsoft_FStar_Backends_OCaml_Syntax.mlmodule1) Support.Microsoft.FStar.Util.either

let mlitem1_ty = (fun mode args -> (match (mode) with
| Sig -> begin
Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_OCaml_Syntax.MLS_Ty (args))
end
| Struct -> begin
Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_OCaml_Syntax.MLM_Ty (args))
end))

let mlitem1_exn = (fun mode args -> (match (mode) with
| Sig -> begin
Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_OCaml_Syntax.MLS_Exn (args))
end
| Struct -> begin
Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_OCaml_Syntax.MLM_Exn (args))
end))

type mldtype =
(Microsoft_FStar_Backends_OCaml_Syntax.mlsymbol * Microsoft_FStar_Backends_OCaml_Syntax.mlidents * Microsoft_FStar_Backends_OCaml_Syntax.mltybody)

type fstypes =
| DT of (string * Microsoft_FStar_Absyn_Syntax.lident list * Microsoft_FStar_Backends_OCaml_Syntax.mlident list * Support.Microsoft.FStar.Range.range)
| Rec of (string * Microsoft_FStar_Absyn_Syntax.ident list * Microsoft_FStar_Absyn_Syntax.lident list * Microsoft_FStar_Backends_OCaml_Syntax.mlident list * Support.Microsoft.FStar.Range.range)
| Abb of (string * Microsoft_FStar_Absyn_Syntax.typ * (tenv * Microsoft_FStar_Backends_OCaml_Syntax.mlident list) * Support.Microsoft.FStar.Range.range)

let mldtype_of_indt = (fun mlenv indt -> (let rec getRecordFieldsFromType = (fun _52_14 -> (match (_52_14) with
| [] -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.RecordType (f)::_ -> begin
Some (f)
end
| _::qualif -> begin
(getRecordFieldsFromType qualif)
end))
in (let rec comp_vars = (fun ct -> (match (ct) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(type_vars t.Microsoft_FStar_Absyn_Syntax.n)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(type_vars ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.n)
end))
and type_vars = (fun ty -> (match (ty) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(Support.List.append ((Support.List.collect (fun _52_15 -> (match (_52_15) with
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(let tl = (type_vars x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n)
in (let hd = if (Microsoft_FStar_Absyn_Syntax.is_null_binder (Support.Microsoft.FStar.Util.Inr (x), None)) then begin
None
end else begin
Some (x.Microsoft_FStar_Absyn_Syntax.v)
end
in (hd)::[]))
end
| _ -> begin
[]
end))) bs) (comp_vars c.Microsoft_FStar_Absyn_Syntax.n))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t))) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (({Microsoft_FStar_Absyn_Syntax.v = _; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) -> begin
(type_vars t.Microsoft_FStar_Absyn_Syntax.n)
end
| _ -> begin
[]
end))
in (let _52_1342 = (let fold1 = (fun sigelt _52_1273 -> (match (_52_1273) with
| (types, ctors) -> begin
(match (sigelt) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((x, tps, k, ts, cs, qualif, rg)) -> begin
if (Support.List.contains Microsoft_FStar_Absyn_Syntax.Logic qualif) then begin
(types, ctors)
end else begin
(let ar = (match ((mlkind_of_kind tps k)) with
| None -> begin
(unsupported rg "not-an-ML-kind")
end
| Some (ar) -> begin
ar
end)
in (let ty = (match (((getRecordFieldsFromType qualif), cs)) with
| (Some (f), c::[]) -> begin
(let _52_1292 = (Support.Microsoft.FStar.Util.smap_add record_constructors c.Microsoft_FStar_Absyn_Syntax.str f)
in Rec ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, f, cs, (Support.Prims.snd (tenv_of_tvmap ar)), rg)))
end
| (_, _) -> begin
DT ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, cs, (Support.Prims.snd (tenv_of_tvmap ar)), rg))
end)
in ((ty)::types, ctors)))
end
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, pr, _, _, rg)) -> begin
(let actr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let anames = (Support.List.map (fun _52_16 -> (match (_52_16) with
| None -> begin
(let _52_1313 = (Support.Microsoft.FStar.Util.incr actr)
in (Support.String.strcat "_" (Support.Microsoft.FStar.Util.string_of_int (! (actr)))))
end
| Some (x) -> begin
(let _52_1317 = (Support.Microsoft.FStar.Util.incr actr)
in x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end)) (type_vars ty.Microsoft_FStar_Absyn_Syntax.n))
in (let _52_1320 = (Support.Microsoft.FStar.Util.smap_add algebraic_constructors x.Microsoft_FStar_Absyn_Syntax.str ((Support.List.length anames), anames))
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
in ((Abb ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, body, (tenv_of_tvmap ar), rg)))::types, ctors))
end
| _ -> begin
(unexpected (Microsoft_FStar_Absyn_Util.range_of_sigelt sigelt) "no-dtype-or-abbrvs-in-bundle")
end)
end))
in (let _52_1339 = (Support.List.fold_right fold1 indt ([], []))
in (match (_52_1339) with
| (ts, cs) -> begin
(ts, (Support.Microsoft.FStar.Util.smap_of_list cs))
end)))
in (match (_52_1342) with
| (ts, cs) -> begin
(let cons_args = (fun cname tparams rg x -> (let _52_1351 = ((Support.Microsoft.FStar.Util.must) (Support.Microsoft.FStar.Util.smap_try_find cs cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText))
in (match (_52_1351) with
| (c, _) -> begin
(let _52_1355 = (strip_polymorphism [] rg c)
in (match (_52_1355) with
| (cparams, rgty, c) -> begin
(let _52_1356 = if ((Support.List.length cparams) <> (Support.List.length tparams)) then begin
(unexpected rg "invalid-number-of-ctor-params")
end
in (let cparams = (Support.List.map (fun _52_1361 -> (match (_52_1361) with
| (x, _) -> begin
x.Microsoft_FStar_Absyn_Syntax.idText
end)) cparams)
in (let tenv = (Support.List.zip cparams tparams)
in (let tenv = TEnv ((Support.Microsoft.FStar.Util.smap_of_list tenv))
in (let c = (mlty_of_ty mlenv tenv (rgty, c))
in (let _52_1368 = (mltycons_of_mlty c)
in (match (_52_1368) with
| (args, name) -> begin
(match (name) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Named ((tyargs, name)) when ((Support.Prims.snd name) = x) -> begin
(let check = (fun x mty -> (match (mty) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Var (mtyx) -> begin
(x = mtyx)
end
| _ -> begin
false
end))
in (let _52_1380 = if ((Support.List.length tyargs) <> (Support.List.length cparams)) then begin
(unexpected rg "dtype-invalid-ctor-result")
end
in (let _52_1382 = if (not ((Support.List.forall2 check tparams tyargs))) then begin
(unsupported rg "dtype-invalid-ctor-result")
end
in args)))
end
| _ -> begin
(unexpected rg "dtype-invalid-ctor-result")
end)
end)))))))
end))
end)))
in (let fortype = (fun ty -> (match (ty) with
| DT ((x, tcs, tparams, rg)) -> begin
(let mldcons_of_cons = (fun cname -> (let args = (cons_args cname tparams rg x)
in (cname.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))
in (x, tparams, Microsoft_FStar_Backends_OCaml_Syntax.MLTD_DType ((Support.List.map mldcons_of_cons tcs))))
end
| Rec ((x, f, tcs, tparams, rg)) -> begin
(let args = (match (tcs) with
| cname::[] -> begin
(cons_args cname tparams rg x)
end
| _ -> begin
(unexpected rg "records-should-have-one-single-constructor")
end)
in (let mldproj_of_proj = (fun name c -> (name.Microsoft_FStar_Absyn_Syntax.idText, c))
in (let _52_1413 = if ((Support.List.length f) <> (Support.List.length args)) then begin
(unexpected rg (Support.Microsoft.FStar.Util.format4 "%s, %s, %s fields, %s args" x (Support.List.hd tcs).Microsoft_FStar_Absyn_Syntax.str ((Support.String.concat ", ") (Support.List.map (fun f -> f.Microsoft_FStar_Absyn_Syntax.idText) f)) (Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))))
end
in (x, tparams, Microsoft_FStar_Backends_OCaml_Syntax.MLTD_Record ((Support.List.map2 mldproj_of_proj f args))))))
end
| Abb ((x, body, (tenv, tparams), rg)) -> begin
(let body = (mlty_of_ty mlenv tenv (rg, body))
in (x, tparams, Microsoft_FStar_Backends_OCaml_Syntax.MLTD_Abbrev (body)))
end))
in (Support.List.map fortype ts)))
end)))))

let mlmod1_of_mod1 = (fun mode mlenv modx -> (let export_val = (fun qal -> (let export_val1 = (fun _52_17 -> (match (_52_17) with
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
(let _52_1452 = (mlscheme_of_ty mlenv rg ty)
in (match (_52_1452) with
| (tparams, ty) -> begin
Some (Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_OCaml_Syntax.MLS_Val ((x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, (tparams, ty)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((x, ty, qal, rg)) when (mode = Sig) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((rec_, lbs), rg, _, _)) when (mode = Struct) -> begin
(let downct = (fun _52_1474 -> (match (_52_1474) with
| (x, _, e) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(x, e)
end
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(unexpected rg "expr-top-let-with-bvar")
end)
end))
in (let lbs = (Support.List.map downct lbs)
in (let lbs = (Support.List.map (fun _52_1483 -> (match (_52_1483) with
| (x, e) -> begin
(x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, [], (mlexpr_of_expr mlenv rg (lenv_of_mlenv mlenv) e))
end)) lbs)
in Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_OCaml_Syntax.MLM_Let ((rec_, lbs)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, rg)) when (mode = Struct) -> begin
(let lenv = (lenv_of_mlenv mlenv)
in Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_OCaml_Syntax.MLM_Top ((mlexpr_of_expr mlenv rg lenv e)))))
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
in (let _52_1518 = (tenv_of_tvmap ar)
in (match (_52_1518) with
| (tenv, tparams) -> begin
(let ty = (mlty_of_ty mlenv tenv (rg, ty))
in (let ty = Microsoft_FStar_Backends_OCaml_Syntax.MLTD_Abbrev (ty)
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
in (let _52_1536 = (tenv_of_tvmap ar)
in (match (_52_1536) with
| (_tenv, tparams) -> begin
Some ((mlitem1_ty mode (((t.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, tparams, None))::[])))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
(unsupported (Microsoft_FStar_Absyn_Util.range_of_sigelt modx) "mod1-effect/kind")
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, _, qal, _, _))::[], _, _, _)) when (not ((export_val qal))) -> begin
None
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((Microsoft_FStar_Absyn_Syntax.Sig_datacon ((x, ty, (tx, _, _), qal, _, rg))::[], _, _, _)) when ((as_tprims tx) = Some (Exn)) -> begin
(let rec aux = (fun acc ty -> (match ((Microsoft_FStar_Absyn_Util.compress_typ ty).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let tys = ((Support.List.collect (fun _52_18 -> (match (_52_18) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort)::[]
end))) bs)
in tys)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (x) when ((as_tprims x.Microsoft_FStar_Absyn_Syntax.v) = Some (Exn)) -> begin
(Support.List.rev acc)
end
| _ -> begin
(unexpected rg "invalid-exn-type")
end))
in (let args = (aux [] ty)
in (let tenv = (Support.Prims.fst (tenv_of_tvmap []))
in (let args = (Support.List.map (fun ty -> (mlty_of_ty mlenv tenv (rg, ty))) args)
in Some ((mlitem1_exn mode (x.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, args)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((indt, _, _, _)) -> begin
(let aout = (mldtype_of_indt mlenv indt)
in (let aout = (Support.List.map (fun _52_1635 -> (match (_52_1635) with
| (x, y, z) -> begin
(x, y, Some (z))
end)) aout)
in (match (mode) with
| Sig -> begin
Some (Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Backends_OCaml_Syntax.MLS_Ty (aout)))
end
| Struct -> begin
Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Backends_OCaml_Syntax.MLM_Ty (aout)))
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

let mlmod_of_mod = (fun mlenv modx -> (let asright = (fun _52_19 -> (match (_52_19) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(failwith "asright")
end))
in (Support.List.choose (fun x -> (Support.Option.map asright (mlmod1_of_mod1 Struct mlenv x))) modx)))

let mlsig_of_sig = (fun mlenv modx -> (let asleft = (fun _52_20 -> (match (_52_20) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x
end
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(failwith "asleft")
end))
in (Support.List.choose (fun x -> (Support.Option.map asleft (mlmod1_of_mod1 Sig mlenv x))) modx)))

let mlmod_of_fstar = (fun fmod_ -> (let name = (Microsoft_FStar_Backends_OCaml_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _52_1679 = (Support.Microsoft.FStar.Util.fprint1 "OCaml: %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in (let mod_ = (mlmod_of_mod (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (let sig_ = (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)
in (name, sig_, mod_))))))

let mlmod_of_iface = (fun fmod_ -> (let name = (Microsoft_FStar_Backends_OCaml_Syntax.mlpath_of_lident fmod_.Microsoft_FStar_Absyn_Syntax.name)
in (let _52_1685 = (Support.Microsoft.FStar.Util.fprint1 "OCaml skip: %s\n" fmod_.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)
in ((Support.Prims.ignore) (mlsig_of_sig (mk_mlenv name) fmod_.Microsoft_FStar_Absyn_Syntax.declarations)))))

let mllib_empty = Microsoft_FStar_Backends_OCaml_Syntax.MLLib ([])

let rec mllib_add = (fun _52_1688 _52_1692 -> (match ((_52_1688, _52_1692)) with
| (Microsoft_FStar_Backends_OCaml_Syntax.MLLib (mllib), (path, sig_, mod_)) -> begin
(let n = (Support.String.concat "_" (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[])))
in (let rec aux = (fun _52_21 -> (match (_52_21) with
| [] -> begin
((n, Some ((sig_, mod_)), mllib_empty))::[]
end
| (name, None, sublibs)::tl -> begin
(let the = (name, None, sublibs)
in if (name = (Support.Prims.snd path)) then begin
((name, Some ((sig_, mod_)), sublibs))::tl
end else begin
(the)::(aux tl)
end)
end
| (name, Some ((ssig, mmod)), sublibs)::tl -> begin
(let the = (name, Some ((ssig, mmod)), sublibs)
in if (name = (Support.Prims.snd path)) then begin
((name, Some ((ssig, mod_)), sublibs))::tl
end else begin
(the)::(aux tl)
end)
end))
in Microsoft_FStar_Backends_OCaml_Syntax.MLLib ((aux mllib))))
end))

let mlmod_of_fstars = (fun fmods -> (let in_std_ns = (fun x -> (Support.Microsoft.FStar.Util.for_some (fun y -> (in_ns (y, x))) (! (Microsoft_FStar_Options.codegen_libs))))
in (let fmods = (Support.List.filter (fun x -> (not ((in_std_ns (Support.List.map (fun y -> y.Microsoft_FStar_Absyn_Syntax.idText) x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.ns))))) fmods)
in (let stdlib = (Support.List.map (fun x -> (Support.Microsoft.FStar.Util.concat_l "." x)) outmod)
in (let extlib = (Support.List.map (fun x -> (Support.Microsoft.FStar.Util.concat_l "." x)) (! (Microsoft_FStar_Options.codegen_libs)))
in (let fmods = (Support.List.filter (fun x -> (not ((Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str stdlib)))) fmods)
in (let fmods = (Support.List.choose (fun x -> if (Support.List.contains x.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str extlib) then begin
(let _52_1728 = (mlmod_of_iface x)
in None)
end else begin
Some ((mlmod_of_fstar x))
end) fmods)
in (let for1 = (fun mllib the -> (let _52_1737 = the
in (match (_52_1737) with
| (path, sig_, mod_) -> begin
(let modname = (Support.List.append (Support.Prims.fst path) (((Support.Prims.snd path))::[]))
in (let rec checkname = (fun modname fbd -> (match ((modname, fbd)) with
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




