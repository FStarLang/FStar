
open Prims
type binding =
| Ty of (FStar_Absyn_Syntax.btvar * FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
| Bv of (FStar_Absyn_Syntax.bvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme)
| Fv of (FStar_Absyn_Syntax.fvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme)

let is_Ty = (fun _discr_ -> (match (_discr_) with
| Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))

let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))

let ___Ty____0 = (fun projectee -> (match (projectee) with
| Ty (_57_6) -> begin
_57_6
end))

let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_57_9) -> begin
_57_9
end))

let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_57_12) -> begin
_57_12
end))

type env =
{tcenv : FStar_Tc_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}

let is_Mkenv = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv")))

let debug = (fun g f -> (match ((((FStar_ST.read FStar_Options.debug) <> []) && ((let _122_65 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.contains "Prims" _122_65)) || (g.currentModule <> ([], "Prims"))))) with
| true -> begin
(f ())
end
| false -> begin
()
end))

let mkFvvar = (fun l t -> (let _122_70 = (FStar_Range.mk_range "" 0 0)
in {FStar_Absyn_Syntax.v = l; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _122_70}))

let erasedContent = FStar_Extraction_ML_Syntax.ml_unit_ty

let erasableTypeNoDelta = (fun t -> (match (t) with
| _57_24 -> begin
(match ((t = FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| false -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_57_26, ("FStar"::"Ghost"::[], "erased")) -> begin
true
end
| _57_35 -> begin
false
end)
end)
end))

let unknownType = FStar_Extraction_ML_Syntax.MLTY_Top

let prependTick = (fun _57_38 -> (match (_57_38) with
| (x, n) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(x, n)
end
| false -> begin
((Prims.strcat "\' " x), n)
end)
end))

let removeTick = (fun _57_41 -> (match (_57_41) with
| (x, n) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(let _122_75 = (FStar_Util.substring_from x 1)
in (_122_75, n))
end
| false -> begin
(x, n)
end)
end))

let convRange = (fun r -> 0)

let convIdent = (fun id -> (id.FStar_Absyn_Syntax.idText, (convRange id.FStar_Absyn_Syntax.idRange)))

let btvar_as_mltyvar = (fun btv -> (prependTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

let btvar_as_mlTermVar = (fun btv -> (removeTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

let rec lookup_ty_local = (fun gamma b -> (match (gamma) with
| Ty (bt, mli, mlt)::tl -> begin
(match ((FStar_Absyn_Util.bvd_eq bt.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)) with
| true -> begin
mlt
end
| false -> begin
(lookup_ty_local tl b)
end)
end
| _57_57::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText))
end))

let tyscheme_of_td = (fun _57_64 -> (match (_57_64) with
| (_57_61, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some ((vars, t))
end
| _57_69 -> begin
None
end)
end))

let lookup_ty_const = (fun env _57_73 -> (match (_57_73) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _57_76 -> (match (_57_76) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(FStar_Util.find_map tds (fun td -> (let _57_83 = td
in (match (_57_83) with
| (n, _57_80, _57_82) -> begin
(match ((n = ty_name)) with
| true -> begin
(tyscheme_of_td td)
end
| false -> begin
None
end)
end))))
end
| false -> begin
None
end)
end)))
end))

let lookup_tyvar = (fun g bt -> (lookup_ty_local g.gamma bt))

let lookup_fv_by_lid = (fun g fv -> (let x = (FStar_Util.find_map g.gamma (fun _57_1 -> (match (_57_1) with
| Fv (fv', path, sc) when (FStar_Absyn_Syntax.lid_equals fv fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _57_95 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _122_105 = (let _122_104 = (FStar_Absyn_Print.sli fv)
in (FStar_Util.format1 "free Variable %s not found\n" _122_104))
in (FStar_All.failwith _122_105))
end
| Some (y) -> begin
y
end)))

let lookup_fv = (fun g fv -> (let x = (FStar_Util.find_map g.gamma (fun _57_2 -> (match (_57_2) with
| Fv (fv', path, sc) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _57_109 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _122_113 = (let _122_112 = (FStar_Range.string_of_range fv.FStar_Absyn_Syntax.p)
in (let _122_111 = (FStar_Absyn_Print.sli fv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _122_112 _122_111)))
in (FStar_All.failwith _122_113))
end
| Some (y) -> begin
y
end)))

let lookup_bv = (fun g bv -> (let x = (FStar_Util.find_map g.gamma (fun _57_3 -> (match (_57_3) with
| Bv (bv', id, sc) when (FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc))
end
| _57_123 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _122_121 = (let _122_120 = (FStar_Range.string_of_range bv.FStar_Absyn_Syntax.p)
in (let _122_119 = (FStar_Absyn_Print.strBvd bv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _122_120 _122_119)))
in (FStar_All.failwith _122_121))
end
| Some (y) -> begin
y
end)))

let lookup = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(lookup_bv g x)
end
| FStar_Util.Inr (x) -> begin
(lookup_fv g x)
end))

let lookup_var = (fun g e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _122_128 = (lookup g (FStar_Util.Inl (x)))
in (_122_128, None))
end
| FStar_Absyn_Syntax.Exp_fvar (x, b) -> begin
(let _122_129 = (lookup g (FStar_Util.Inr (x)))
in (_122_129, b))
end
| _57_143 -> begin
(FStar_All.failwith "impossible")
end))

let extend_ty = (fun g a mapped_to -> (let ml_a = (btvar_as_mltyvar a)
in (let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (let gamma = (Ty ((a, ml_a, mapped_to)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))))
in (let _57_154 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _57_154.tydefs; currentModule = _57_154.currentModule}))))))

let extend_bv = (fun g x t_x add_unit mk_unit -> (let mlx = FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))
in (let mlx = (match (mk_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| false -> begin
(match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLE_App ((mlx, (FStar_Extraction_ML_Syntax.ml_unit)::[]))
end
| false -> begin
mlx
end)
end)
in (let gamma = (Bv ((x, mlx, t_x)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let _57_165 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _57_165.tydefs; currentModule = _57_165.currentModule}))))))

let rec mltyFvars = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _122_149 = (mltyFvars t1)
in (let _122_148 = (mltyFvars t2)
in (FStar_List.append _122_149 _122_148)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(FStar_List.collect mltyFvars args)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(FStar_List.collect mltyFvars ts)
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
[]
end))

let rec subsetMlidents = (fun la lb -> (match (la) with
| h::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

let tySchemeIsClosed = (fun tys -> (let _122_156 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _122_156 (Prims.fst tys))))

let extend_fv' = (fun g x y t_x add_unit -> (match ((tySchemeIsClosed t_x)) with
| true -> begin
(let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (let mly = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLE_App ((mly, (FStar_Extraction_ML_Syntax.ml_unit)::[]))
end
| false -> begin
mly
end)
in (let gamma = (Fv ((x, mly, t_x)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_lid ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let _57_198 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _57_198.tydefs; currentModule = _57_198.currentModule})))))
end
| false -> begin
(FStar_All.failwith "freevars found")
end))

let extend_fv = (fun g x t_x add_unit -> (let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit)))

let extend_lb = (fun g l t t_x add_unit -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _122_185 = (extend_bv g (FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit false)
in (_122_185, (FStar_Extraction_ML_Syntax.as_mlident x)))
end
| FStar_Util.Inr (f) -> begin
(let _57_216 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_57_216) with
| (p, y) -> begin
(let _122_187 = (let _122_186 = (FStar_Absyn_Util.fvvar_of_lid f t)
in (extend_fv' g _122_186 (p, y) t_x add_unit))
in (_122_187, (y, 0)))
end))
end))

let extend_tydef = (fun g td -> (let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (let _57_220 = g
in {tcenv = _57_220.tcenv; gamma = _57_220.gamma; tydefs = ((m, td))::g.tydefs; currentModule = _57_220.currentModule})))

let emptyMlPath = ([], "")

let mkContext = (fun e -> (let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (let a = ("\'a", (- (1)))
in (let failwith_ty = ((a)::[], FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.MLTY_Var (a))))
in (let _122_194 = (extend_lb env (FStar_Util.Inr (FStar_Absyn_Const.failwith_lid)) FStar_Absyn_Syntax.tun failwith_ty false)
in (FStar_All.pipe_right _122_194 Prims.fst))))))
