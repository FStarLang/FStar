
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
Microsoft_FStar_Backends_ML_Syntax.MLC_Int32 ((Support.Microsoft.FStar.Util.int32_of_int (Support.Microsoft.FStar.Util.int_of_string c)))
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
((Support.Prims.snd) ((Support.Microsoft.FStar.Util.must) (Support.Microsoft.FStar.Util.find_opt (fun ( _52_43 ) -> (match (_52_43) with
| (y, _) -> begin
(y = x)
end)) subst)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, f, t2)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun (((subst_aux subst t1), f, (subst_aux subst t2)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, path)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (((Support.List.map (subst_aux subst) args), path))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (ts) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple ((Support.List.map (subst_aux subst) ts))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_App (((subst_aux subst t1), (subst_aux subst t2)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Top
end))

let subst = (fun ( _52_62 ) ( args ) -> (match (_52_62) with
| (formals, t) -> begin
if ((Support.List.length formals) <> (Support.List.length args)) then begin
(failwith "Substitution must be fully applied")
end else begin
(subst_aux (Support.List.zip formals args) t)
end
end))

let delta_unfold = (fun ( g ) ( t ) -> None)

let rec equiv = (fun ( g ) ( t ) ( t' ) -> (match ((t, t')) with
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (x), Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (y)) -> begin
((Support.Prims.fst x) = (Support.Prims.fst y))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, f, t2)), Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1', f', t2'))) -> begin
((equiv g t1 t1') && (equiv g t2 t2'))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, path)), Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args', path'))) when (path = path') -> begin
(Support.List.forall2 (equiv g) args args')
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
| Some (t) -> begin
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

let is_type_abstraction = (fun ( _52_1 ) -> (match (_52_1) with
| (Support.Microsoft.FStar.Util.Inl (_), _)::_ -> begin
true
end
| _ -> begin
false
end))

let mkTypFun = (fun ( bs ) ( c ) ( original ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None original.Microsoft_FStar_Absyn_Syntax.pos))

let mkTypApp = (fun ( typ ) ( arrgs ) ( original ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (typ, arrgs) None original.Microsoft_FStar_Absyn_Syntax.pos))

let tbinder_prefix = (fun ( t ) -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((Support.Microsoft.FStar.Util.prefix_until (fun ( _52_2 ) -> (match (_52_2) with
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
(bs, (mkTypFun ((b)::rest) c t))
end)
end
| _ -> begin
([], t)
end))




