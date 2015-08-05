
let pruneNones = (fun ( l ) -> (Support.List.fold_right (fun ( x ) ( ll ) -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))

let mlconst_of_const = (fun ( sctt ) -> (match (sctt) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Unit
end
| Microsoft_FStar_Absyn_Syntax.Const_char (c) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Char (c)
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (c) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Byte (c)
end
| Microsoft_FStar_Absyn_Syntax.Const_int (c) -> begin
(let _68_24255 = (let _68_24254 = (Support.Microsoft.FStar.Util.int_of_string c)
in (Support.Microsoft.FStar.Util.int32_of_int _68_24254))
in Microsoft_FStar_Extraction_ML_Syntax.MLC_Int32 (_68_24255))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Int32 (i)
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (i) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Int64 (i)
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (b)
end
| Microsoft_FStar_Absyn_Syntax.Const_float (d) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Float (d)
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray ((bytes, _55_30)) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _55_35)) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLC_String ((Support.Microsoft.FStar.Util.string_of_unicode bytes))
end))

let rec subst_aux = (fun ( subst ) ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(match ((Support.Microsoft.FStar.Util.find_opt (fun ( _55_45 ) -> (match (_55_45) with
| (y, _55_44) -> begin
(y = x)
end)) subst)) with
| Some (ts) -> begin
(Support.Prims.snd ts)
end
| None -> begin
t
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, f, t2)) -> begin
(let _68_24263 = (let _68_24262 = (subst_aux subst t1)
in (let _68_24261 = (subst_aux subst t2)
in (_68_24262, f, _68_24261)))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_68_24263))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, path)) -> begin
(let _68_24265 = (let _68_24264 = (Support.List.map (subst_aux subst) args)
in (_68_24264, path))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (_68_24265))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _68_24266 = (Support.List.map (subst_aux subst) ts)
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (_68_24266))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let _68_24269 = (let _68_24268 = (subst_aux subst t1)
in (let _68_24267 = (subst_aux subst t2)
in (_68_24268, _68_24267)))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_App (_68_24269))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top
end))

let subst = (fun ( _55_67 ) ( args ) -> (match (_55_67) with
| (formals, t) -> begin
(match (((Support.List.length formals) <> (Support.List.length args))) with
| true -> begin
(failwith ("Substitution must be fully applied"))
end
| false -> begin
(let _68_24274 = (Support.List.zip formals args)
in (subst_aux _68_24274 t))
end)
end))

let delta_unfold = (fun ( g ) ( _55_1 ) -> (match (_55_1) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, n)) -> begin
(match ((Microsoft_FStar_Extraction_ML_Env.lookup_ty_const g n)) with
| Some (ts) -> begin
(let _68_24279 = (subst ts args)
in Some (_68_24279))
end
| _55_78 -> begin
None
end)
end
| _55_80 -> begin
None
end))

let rec equiv = (fun ( g ) ( t ) ( t' ) -> (match ((t, t')) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (x), Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
((Support.Prims.fst x) = (Support.Prims.fst y))
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, f, t2)), Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1', f', t2'))) -> begin
((equiv g t1 t1') && (equiv g t2 t2'))
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, path)), Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args', path'))) -> begin
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
| (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
(Support.List.forall2 (equiv g) ts ts')
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
true
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (_55_124), _55_127) -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(equiv g t t')
end
| _55_132 -> begin
false
end)
end
| (_55_134, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (_55_136)) -> begin
(match ((delta_unfold g t')) with
| Some (t') -> begin
(equiv g t t')
end
| _55_142 -> begin
false
end)
end
| _55_144 -> begin
false
end))

let unit_binder = (let x = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Tc_Recheck.t_unit)
in (Microsoft_FStar_Absyn_Syntax.v_binder x))

let is_type_abstraction = (fun ( _55_2 ) -> (match (_55_2) with
| (Support.Microsoft.FStar.Util.Inl (_55_150), _55_153)::_55_148 -> begin
true
end
| _55_157 -> begin
false
end))

let mkTypFun = (fun ( bs ) ( c ) ( original ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.Microsoft_FStar_Absyn_Syntax.pos))

let mkTypApp = (fun ( typ ) ( arrgs ) ( original ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.Microsoft_FStar_Absyn_Syntax.pos))

let tbinder_prefix = (fun ( t ) -> (match ((let _68_24301 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_24301.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _55_3 ) -> (match (_55_3) with
| (Support.Microsoft.FStar.Util.Inr (_55_171), _55_174) -> begin
true
end
| _55_177 -> begin
false
end)) bs)) with
| None -> begin
(bs, t)
end
| Some ((bs, b, rest)) -> begin
(let _68_24303 = (mkTypFun ((b)::rest) c t)
in (bs, _68_24303))
end)
end
| _55_185 -> begin
([], t)
end))

let is_xtuple = (fun ( _55_188 ) -> (match (_55_188) with
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
| _55_196 -> begin
None
end)
end
| false -> begin
None
end)
end))

let resugar_exp = (fun ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((mlp, args)) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (args)
end
| _55_205 -> begin
e
end)
end
| _55_207 -> begin
e
end))

let record_field_path = (fun ( _55_4 ) -> (match (_55_4) with
| f::_55_210 -> begin
(let _55_216 = (Support.Microsoft.FStar.Util.prefix f.Microsoft_FStar_Absyn_Syntax.ns)
in (match (_55_216) with
| (ns, _55_215) -> begin
(Support.Prims.pipe_right ns (Support.List.map (fun ( id ) -> id.Microsoft_FStar_Absyn_Syntax.idText)))
end))
end
| _55_219 -> begin
(failwith ("impos"))
end))

let record_fields = (fun ( fs ) ( vs ) -> (Support.List.map2 (fun ( f ) ( e ) -> (f.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText, e)) fs vs))

let resugar_pat = (fun ( q ) ( p ) -> (match (p) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((d, pats)) -> begin
(match ((is_xtuple d)) with
| Some (n) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _55_233 -> begin
(match (q) with
| Some (Microsoft_FStar_Absyn_Syntax.Record_ctor ((_55_235, fns))) -> begin
(let p = (record_field_path fns)
in (let fs = (record_fields fns pats)
in Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((p, fs))))
end
| _55_243 -> begin
p
end)
end)
end
| _55_245 -> begin
p
end))

let is_xtuple_ty = (fun ( _55_248 ) -> (match (_55_248) with
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
| _55_256 -> begin
None
end)
end
| false -> begin
None
end)
end))

let resugar_mlty = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, mlp)) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| _55_265 -> begin
t
end)
end
| _55_267 -> begin
t
end))

let flatten_ns = (fun ( ns ) -> (Support.String.concat "_" ns))

let flatten_mlpath = (fun ( _55_271 ) -> (match (_55_271) with
| (ns, n) -> begin
(Support.String.concat "_" (Support.List.append ns ((n)::[])))
end))

let mlpath_of_lid = (fun ( l ) -> (let _68_24330 = (Support.Prims.pipe_right l.Microsoft_FStar_Absyn_Syntax.ns (Support.List.map (fun ( i ) -> i.Microsoft_FStar_Absyn_Syntax.idText)))
in (_68_24330, l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))

let rec erasableType = (fun ( g ) ( t ) -> (match ((Microsoft_FStar_Extraction_ML_Env.erasableTypeNoDelta t)) with
| true -> begin
true
end
| false -> begin
(match ((delta_unfold g t)) with
| Some (t) -> begin
(erasableType g t)
end
| None -> begin
false
end)
end))

let rec eraseTypeDeep = (fun ( g ) ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((tyd, etag, tycd)) -> begin
(match ((etag = Microsoft_FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(let _68_24341 = (let _68_24340 = (eraseTypeDeep g tyd)
in (let _68_24339 = (eraseTypeDeep g tycd)
in (_68_24340, etag, _68_24339)))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (_68_24341))
end
| false -> begin
t
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((lty, mlp)) -> begin
(match ((erasableType g t)) with
| true -> begin
Microsoft_FStar_Extraction_ML_Env.erasedContent
end
| false -> begin
(let _68_24343 = (let _68_24342 = (Support.List.map (eraseTypeDeep g) lty)
in (_68_24342, mlp))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (_68_24343))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(let _68_24344 = (Support.List.map (eraseTypeDeep g) lty)
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (_68_24344))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((tyf, tyarg)) -> begin
(let _68_24347 = (let _68_24346 = (eraseTypeDeep g tyf)
in (let _68_24345 = (eraseTypeDeep g tyarg)
in (_68_24346, _68_24345)))
in Microsoft_FStar_Extraction_ML_Syntax.MLTY_App (_68_24347))
end
| _55_297 -> begin
t
end))




