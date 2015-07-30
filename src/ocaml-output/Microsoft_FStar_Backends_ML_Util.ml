
let pruneNones = (fun ( l ) -> (Support.List.fold_right (fun ( x ) ( ll ) -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))

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
(let _65_24243 = (let _65_24242 = (Support.Microsoft.FStar.Util.int_of_string c)
in (Support.Microsoft.FStar.Util.int32_of_int _65_24242))
in Microsoft_FStar_Backends_ML_Syntax.MLC_Int32 (_65_24243))
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
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((bytes, _)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_Bytes (bytes)
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLC_String ((Support.Microsoft.FStar.Util.string_of_unicode bytes))
end))

let rec subst_aux = (fun ( subst ) ( t ) -> (match (t) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (x) -> begin
(match ((Support.Microsoft.FStar.Util.find_opt (fun ( _57_45 ) -> (match (_57_45) with
| (y, _) -> begin
(y = x)
end)) subst)) with
| Some (ts) -> begin
(Support.Prims.snd ts)
end
| None -> begin
t
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, f, t2)) -> begin
(let _65_24251 = (let _65_24250 = (subst_aux subst t1)
in (let _65_24249 = (subst_aux subst t2)
in (_65_24250, f, _65_24249)))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun (_65_24251))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, path)) -> begin
(let _65_24253 = (let _65_24252 = (Support.List.map (subst_aux subst) args)
in (_65_24252, path))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (_65_24253))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _65_24254 = (Support.List.map (subst_aux subst) ts)
in Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (_65_24254))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let _65_24257 = (let _65_24256 = (subst_aux subst t1)
in (let _65_24255 = (subst_aux subst t2)
in (_65_24256, _65_24255)))
in Microsoft_FStar_Backends_ML_Syntax.MLTY_App (_65_24257))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Top
end))

let subst = (fun ( _57_67 ) ( args ) -> (match (_57_67) with
| (formals, t) -> begin
(match (((Support.List.length formals) <> (Support.List.length args))) with
| true -> begin
(failwith ("Substitution must be fully applied"))
end
| false -> begin
(let _65_24262 = (Support.List.zip formals args)
in (subst_aux _65_24262 t))
end)
end))

let delta_unfold = (fun ( g ) ( _57_1 ) -> (match (_57_1) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, n)) -> begin
(match ((Microsoft_FStar_Backends_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _65_24267 = (subst ts args)
in Some (_65_24267))
end
| _ -> begin
None
end)
end
| _ -> begin
None
end))

let rec equiv = (fun ( g ) ( t ) ( t' ) -> (match ((t, t')) with
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (x), Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (y)) -> begin
((Support.Prims.fst x) = (Support.Prims.fst y))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, f, t2)), Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1', f', t2'))) -> begin
((equiv g t1 t1') && (equiv g t2 t2'))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, path)), Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args', path'))) -> begin
(match ((path = path')) with
| true -> begin
(Support.List.forall2 (equiv g) args args')
end
| false -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(equiv g t t')
end
| None -> begin
(match ((delta_unfold g t')) with
| None -> begin
false
end
| Some (t') -> begin
(equiv g t t')
end)
end)
end)
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (ts), Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (ts')) -> begin
(Support.List.forall2 (equiv g) ts ts')
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Top, Microsoft_FStar_Backends_ML_Syntax.MLTY_Top) -> begin
true
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (_), _) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(equiv g t t')
end
| _ -> begin
false
end)
end
| (_, Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (_)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(equiv g t t')
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))

let unit_binder = (let x = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Tc_Recheck.t_unit)
in (Microsoft_FStar_Absyn_Syntax.v_binder x))

let is_type_abstraction = (fun ( _57_2 ) -> (match (_57_2) with
| (Support.Microsoft.FStar.Util.Inl (_), _)::_ -> begin
true
end
| _ -> begin
false
end))

let mkTypFun = (fun ( bs ) ( c ) ( original ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.Microsoft_FStar_Absyn_Syntax.pos))

let mkTypApp = (fun ( typ ) ( arrgs ) ( original ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.Microsoft_FStar_Absyn_Syntax.pos))

let tbinder_prefix = (fun ( t ) -> (match ((let _65_24289 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _65_24289.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _57_3 ) -> (match (_57_3) with
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
true
end
| _ -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some ((bs, b, rest)) -> begin
(let _65_24291 = (mkTypFun ((b)::rest) c t)
in (bs, _65_24291))
end)
end
| _ -> begin
([], t)
end))

let is_xtuple = (fun ( _57_188 ) -> (match (_57_188) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
(match (n) with
| "MkTuple2" -> begin
Some (2)
end
| "MkTuple3" -> begin
Some (3)
end
| "MkTuple4" -> begin
Some (4)
end
| "MkTuple5" -> begin
Some (5)
end
| "MkTuple6" -> begin
Some (6)
end
| "MkTuple7" -> begin
Some (7)
end
| _ -> begin
None
end)
end
| false -> begin
None
end)
end))

let resugar_exp = (fun ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((mlp, args)) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (args)
end
| _ -> begin
e
end)
end
| _ -> begin
e
end))

let record_field_path = (fun ( _57_4 ) -> (match (_57_4) with
| f::_ -> begin
(let _57_216 = (Support.Microsoft.FStar.Util.prefix f.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_57_216) with
| (ns, _) -> begin
(Support.Prims.pipe_right ns (Support.List.map (fun ( id ) -> id.Microsoft_FStar_Absyn_Syntax.idText)))
end))
end
| _ -> begin
(failwith ("impos"))
end))

let record_fields = (fun ( fs ) ( vs ) -> (Support.List.map2 (fun ( f ) ( e ) -> (f.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, e)) fs vs))

let resugar_pat = (fun ( q ) ( p ) -> (match (p) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((d, pats)) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (pats)
end
| _ -> begin
(match (q) with
| Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((_, fns))) -> begin
(let p = (record_field_path fns)
in (let fs = (record_fields fns pats)
in Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((p, fs))))
end
| _ -> begin
p
end)
end)
end
| _ -> begin
p
end))

let is_xtuple_ty = (fun ( _57_248 ) -> (match (_57_248) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
(match (n) with
| "Tuple2" -> begin
Some (2)
end
| "Tuple3" -> begin
Some (3)
end
| "Tuple4" -> begin
Some (4)
end
| "Tuple5" -> begin
Some (5)
end
| "Tuple6" -> begin
Some (6)
end
| "Tuple7" -> begin
Some (7)
end
| _ -> begin
None
end)
end
| false -> begin
None
end)
end))

let resugar_mlty = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, mlp)) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (args)
end
| _ -> begin
t
end)
end
| _ -> begin
t
end))

let flatten_ns = (fun ( ns ) -> (Support.String.concat "_" ns))

let flatten_mlpath = (fun ( _57_271 ) -> (match (_57_271) with
| (ns, n) -> begin
(Support.String.concat "_" (Support.List.append ns ((n)::[])))
end))

let mlpath_of_lid = (fun ( l ) -> (let _65_24318 = (Support.Prims.pipe_right l.Microsoft_FStar_Absyn_Syntax.ns (Support.List.map (fun ( i ) -> i.Microsoft_FStar_Absyn_Syntax.idText)))
in (_65_24318, l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))




