
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
| Ty (_70_6) -> begin
_70_6
end))

let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_70_9) -> begin
_70_9
end))

let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_70_12) -> begin
_70_12
end))

type env =
{tcenv : FStar_Tc_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}

let is_Mkenv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let debug = (fun g f -> if (((FStar_ST.read FStar_Options.debug) <> []) && ((let _147_65 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.contains "Prims" _147_65)) || (g.currentModule <> ([], "Prims")))) then begin
(f ())
end else begin
()
end)

let mkFvvar = (fun l t -> (let _147_70 = (FStar_Range.mk_range "" 0 0)
in {FStar_Absyn_Syntax.v = l; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _147_70}))

let erasedContent = FStar_Extraction_ML_Syntax.ml_unit_ty

let erasableTypeNoDelta = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_70_24, ("FStar"::"Ghost"::[], "erased")) -> begin
true
end
| _70_33 -> begin
false
end)
end)

let unknownType = FStar_Extraction_ML_Syntax.MLTY_Top

let prependTick = (fun _70_36 -> (match (_70_36) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(x, n)
end else begin
((Prims.strcat "\' " x), n)
end
end))

let removeTick = (fun _70_39 -> (match (_70_39) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _147_75 = (FStar_Util.substring_from x 1)
in (_147_75, n))
end else begin
(x, n)
end
end))

let convRange = (fun r -> 0)

let convIdent = (fun id -> (id.FStar_Ident.idText, (convRange id.FStar_Ident.idRange)))

let btvar_as_mltyvar = (fun btv -> (prependTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

let btvar_as_mlTermVar = (fun btv -> (removeTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

let rec lookup_ty_local = (fun gamma b -> (match (gamma) with
| Ty (bt, mli, mlt)::tl -> begin
if (FStar_Absyn_Util.bvd_eq bt.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| _70_55::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText))
end))

let tyscheme_of_td = (fun _70_62 -> (match (_70_62) with
| (_70_59, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some ((vars, t))
end
| _70_67 -> begin
None
end)
end))

let lookup_ty_const = (fun env _70_71 -> (match (_70_71) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _70_74 -> (match (_70_74) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (let _70_81 = td
in (match (_70_81) with
| (n, _70_78, _70_80) -> begin
if (n = ty_name) then begin
(tyscheme_of_td td)
end else begin
None
end
end))))
end else begin
None
end
end)))
end))

let lookup_tyvar = (fun g bt -> (lookup_ty_local g.gamma bt))

let lookup_fv_by_lid = (fun g fv -> (let x = (FStar_Util.find_map g.gamma (fun _70_1 -> (match (_70_1) with
| Fv (fv', path, sc) when (FStar_Ident.lid_equals fv fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _70_93 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _147_105 = (let _147_104 = (FStar_Absyn_Print.sli fv)
in (FStar_Util.format1 "free Variable %s not found\n" _147_104))
in (FStar_All.failwith _147_105))
end
| Some (y) -> begin
y
end)))

let lookup_fv = (fun g fv -> (let x = (FStar_Util.find_map g.gamma (fun _70_2 -> (match (_70_2) with
| Fv (fv', path, sc) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _70_107 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _147_113 = (let _147_112 = (FStar_Range.string_of_range fv.FStar_Absyn_Syntax.p)
in (let _147_111 = (FStar_Absyn_Print.sli fv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _147_112 _147_111)))
in (FStar_All.failwith _147_113))
end
| Some (y) -> begin
y
end)))

let lookup_bv = (fun g bv -> (let x = (FStar_Util.find_map g.gamma (fun _70_3 -> (match (_70_3) with
| Bv (bv', id, sc) when (FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc))
end
| _70_121 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _147_121 = (let _147_120 = (FStar_Range.string_of_range bv.FStar_Absyn_Syntax.p)
in (let _147_119 = (FStar_Absyn_Print.strBvd bv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _147_120 _147_119)))
in (FStar_All.failwith _147_121))
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
(let _147_128 = (lookup g (FStar_Util.Inl (x)))
in (_147_128, None))
end
| FStar_Absyn_Syntax.Exp_fvar (x, b) -> begin
(let _147_129 = (lookup g (FStar_Util.Inr (x)))
in (_147_129, b))
end
| _70_141 -> begin
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
in (let _70_152 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _70_152.tydefs; currentModule = _70_152.currentModule}))))))

let extend_bv = (fun g x t_x add_unit mk_unit -> (let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _70_163 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (let mlx = FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))
in (let mlx = if mk_unit then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx), (FStar_Extraction_ML_Syntax.ml_unit)::[]))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end
end
in (let gamma = (Bv ((x, mlx, t_x)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let _70_169 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _70_169.tydefs; currentModule = _70_169.currentModule})))))))

let rec mltyFvars = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _147_149 = (mltyFvars t1)
in (let _147_148 = (mltyFvars t2)
in (FStar_List.append _147_149 _147_148)))
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

let tySchemeIsClosed = (fun tys -> (let _147_156 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _147_156 (Prims.fst tys))))

let extend_fv' = (fun g x y t_x add_unit -> if (tySchemeIsClosed t_x) then begin
(let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _70_202 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly), (FStar_Extraction_ML_Syntax.ml_unit)::[]))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (let gamma = (Fv ((x, mly, t_x)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_lid ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let _70_208 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _70_208.tydefs; currentModule = _70_208.currentModule}))))))
end else begin
(FStar_All.failwith "freevars found")
end)

let extend_fv = (fun g x t_x add_unit -> (let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit)))

let extend_lb = (fun g l t t_x add_unit -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _147_185 = (extend_bv g (FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit false)
in (_147_185, (FStar_Extraction_ML_Syntax.as_mlident x)))
end
| FStar_Util.Inr (f) -> begin
(let _70_226 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_70_226) with
| (p, y) -> begin
(let _147_186 = (extend_fv' g (FStar_Absyn_Util.fvvar_of_lid f t) (p, y) t_x add_unit)
in (_147_186, (y, 0)))
end))
end))

let extend_tydef = (fun g td -> (let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (let _70_230 = g
in {tcenv = _70_230.tcenv; gamma = _70_230.gamma; tydefs = ((m, td))::g.tydefs; currentModule = _70_230.currentModule})))

let emptyMlPath = ([], "")

let mkContext = (fun e -> (let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (let a = ("\'a", (- (1)))
in (let failwith_ty = ((a)::[], FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.MLTY_Var (a))))
in (let _147_193 = (extend_lb env (FStar_Util.Inr (FStar_Absyn_Const.failwith_lid)) FStar_Absyn_Syntax.tun failwith_ty false)
in (FStar_All.pipe_right _147_193 Prims.fst))))))




