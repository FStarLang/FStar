
type binding =
| Ty of (Microsoft_FStar_Absyn_Syntax.btvar * Microsoft_FStar_Extraction_ML_Syntax.mlident * Microsoft_FStar_Extraction_ML_Syntax.mlty)
| Bv of (Microsoft_FStar_Absyn_Syntax.bvvar * Microsoft_FStar_Extraction_ML_Syntax.mlexpr * Microsoft_FStar_Extraction_ML_Syntax.mltyscheme)
| Fv of (Microsoft_FStar_Absyn_Syntax.fvvar * Microsoft_FStar_Extraction_ML_Syntax.mlexpr * Microsoft_FStar_Extraction_ML_Syntax.mltyscheme)

let is_Ty = (fun ( _discr_ ) -> (match (_discr_) with
| Ty (_) -> begin
true
end
| _ -> begin
false
end))

let is_Bv = (fun ( _discr_ ) -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))

let is_Fv = (fun ( _discr_ ) -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))

let ___Ty____0 = (fun ( projectee ) -> (match (projectee) with
| Ty (_56_6) -> begin
_56_6
end))

let ___Bv____0 = (fun ( projectee ) -> (match (projectee) with
| Bv (_56_9) -> begin
_56_9
end))

let ___Fv____0 = (fun ( projectee ) -> (match (projectee) with
| Fv (_56_12) -> begin
_56_12
end))

type env =
{tcenv : Microsoft_FStar_Tc_Env.env; gamma : binding list; tydefs : (Microsoft_FStar_Extraction_ML_Syntax.mlsymbol list * Microsoft_FStar_Extraction_ML_Syntax.mltydecl) list; currentModule : Microsoft_FStar_Extraction_ML_Syntax.mlpath}

let is_Mkenv = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv"))

let debug = (fun ( g ) ( f ) -> (match ((((Support.ST.read Microsoft_FStar_Options.debug) <> []) && ((let _70_27120 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.List.contains "Prims" _70_27120)) || (g.currentModule <> ([], "Prims"))))) with
| true -> begin
(f ())
end
| false -> begin
()
end))

let mkFvvar = (fun ( l ) ( t ) -> (let _70_27125 = (Support.Microsoft.FStar.Range.mk_range "" 0 0)
in {Microsoft_FStar_Absyn_Syntax.v = l; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _70_27125}))

let erasedContent = Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty

let erasableTypeNoDelta = (fun ( t ) -> (match (t) with
| _56_24 -> begin
(match ((t = Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| false -> begin
(match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((_56_26, ("Ghost"::[], "erased"))) -> begin
true
end
| _56_34 -> begin
false
end)
end)
end))

let unknownType = Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top

let prependTick = (fun ( _56_37 ) -> (match (_56_37) with
| (x, n) -> begin
(match ((Support.Microsoft.FStar.Util.starts_with x "\'")) with
| true -> begin
(x, n)
end
| false -> begin
((Support.String.strcat "\' " x), n)
end)
end))

let removeTick = (fun ( _56_40 ) -> (match (_56_40) with
| (x, n) -> begin
(match ((Support.Microsoft.FStar.Util.starts_with x "\'")) with
| true -> begin
(let _70_27130 = (Support.Microsoft.FStar.Util.substring_from x 1)
in (_70_27130, n))
end
| false -> begin
(x, n)
end)
end))

let convRange = (fun ( r ) -> 0)

let convIdent = (fun ( id ) -> (id.Microsoft_FStar_Absyn_Syntax.idText, (convRange id.Microsoft_FStar_Absyn_Syntax.idRange)))

let btvar_as_mltyvar = (fun ( btv ) -> (prependTick (convIdent btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)))

let btvar_as_mlTermVar = (fun ( btv ) -> (removeTick (convIdent btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)))

let rec lookup_ty_local = (fun ( gamma ) ( b ) -> (match (gamma) with
| Ty ((bt, mli, mlt))::tl -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq bt.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
mlt
end
| false -> begin
(lookup_ty_local tl b)
end)
end
| _56_56::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(Support.All.failwith (Support.String.strcat "extraction: unbound type var " b.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText))
end))

let tyscheme_of_td = (fun ( _56_63 ) -> (match (_56_63) with
| (_56_60, vars, body_opt) -> begin
(match (body_opt) with
| Some (Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some ((vars, t))
end
| _56_68 -> begin
None
end)
end))

let lookup_ty_const = (fun ( env ) ( _56_72 ) -> (match (_56_72) with
| (module_name, ty_name) -> begin
(Support.Microsoft.FStar.Util.find_map env.tydefs (fun ( _56_75 ) -> (match (_56_75) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(Support.Microsoft.FStar.Util.find_map tds (fun ( td ) -> (let _56_82 = td
in (match (_56_82) with
| (n, _56_79, _56_81) -> begin
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

let lookup_tyvar = (fun ( g ) ( bt ) -> (lookup_ty_local g.gamma bt))

let lookup_fv_by_lid = (fun ( g ) ( fv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _56_1 ) -> (match (_56_1) with
| Fv ((fv', path, sc)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv fv'.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _56_94 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _70_27160 = (let _70_27159 = (Microsoft_FStar_Absyn_Print.sli fv)
in (Support.Microsoft.FStar.Util.format1 "free Variable %s not found\n" _70_27159))
in (Support.All.failwith _70_27160))
end
| Some (y) -> begin
y
end)))

let lookup_fv = (fun ( g ) ( fv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _56_2 ) -> (match (_56_2) with
| Fv ((fv', path, sc)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v fv'.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _56_108 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _70_27168 = (let _70_27167 = (Support.Microsoft.FStar.Range.string_of_range fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_27166 = (Microsoft_FStar_Absyn_Print.sli fv.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "(%s) free Variable %s not found\n" _70_27167 _70_27166)))
in (Support.All.failwith _70_27168))
end
| Some (y) -> begin
y
end)))

let lookup_bv = (fun ( g ) ( bv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _56_3 ) -> (match (_56_3) with
| Bv ((bv', id, sc)) when (Microsoft_FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc))
end
| _56_122 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _70_27176 = (let _70_27175 = (Support.Microsoft.FStar.Range.string_of_range bv.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_27174 = (Microsoft_FStar_Absyn_Print.strBvd bv.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "(%s) bound Variable %s not found\n" _70_27175 _70_27174)))
in (Support.All.failwith _70_27176))
end
| Some (y) -> begin
y
end)))

let lookup = (fun ( g ) ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(lookup_bv g x)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(lookup_fv g x)
end))

let lookup_var = (fun ( g ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _70_27183 = (lookup g (Support.Microsoft.FStar.Util.Inl (x)))
in (_70_27183, None))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, b)) -> begin
(let _70_27184 = (lookup g (Support.Microsoft.FStar.Util.Inr (x)))
in (_70_27184, b))
end
| _56_142 -> begin
(Support.All.failwith "impossible")
end))

let extend_ty = (fun ( g ) ( a ) ( mapped_to ) -> (let ml_a = (btvar_as_mltyvar a)
in (let mapped_to = (match (mapped_to) with
| None -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (let gamma = (Ty ((a, ml_a, mapped_to)))::g.gamma
in (let tcenv = (Microsoft_FStar_Tc_Env.push_local_binding g.tcenv (Microsoft_FStar_Tc_Env.Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, a.Microsoft_FStar_Absyn_Syntax.sort))))
in (let _56_153 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _56_153.tydefs; currentModule = _56_153.currentModule}))))))

let extend_bv = (fun ( g ) ( x ) ( t_x ) ( add_unit ) -> (let mlx = Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((Microsoft_FStar_Extraction_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v))
in (let mlx = (match (add_unit) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((mlx, (Microsoft_FStar_Extraction_ML_Syntax.ml_unit)::[]))
end
| false -> begin
mlx
end)
in (let gamma = (Bv ((x, mlx, t_x)))::g.gamma
in (let tcenv = (Microsoft_FStar_Tc_Env.push_local_binding g.tcenv (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let _56_163 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _56_163.tydefs; currentModule = _56_163.currentModule}))))))

let rec mltyFvars = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, f, t2)) -> begin
(let _70_27202 = (mltyFvars t1)
in (let _70_27201 = (mltyFvars t2)
in (Support.List.append _70_27202 _70_27201)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, path)) -> begin
(Support.List.collect mltyFvars args)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(Support.List.collect mltyFvars ts)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let _70_27204 = (mltyFvars t1)
in (let _70_27203 = (mltyFvars t2)
in (Support.List.append _70_27204 _70_27203)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
[]
end))

let rec subsetMlidents = (fun ( la ) ( lb ) -> (match (la) with
| h::tla -> begin
((Support.List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

let tySchemeIsClosed = (fun ( tys ) -> (let _70_27211 = (mltyFvars (Support.Prims.snd tys))
in (subsetMlidents _70_27211 (Support.Prims.fst tys))))

let extend_fv' = (fun ( g ) ( x ) ( y ) ( t_x ) ( add_unit ) -> (match ((tySchemeIsClosed t_x)) with
| true -> begin
(let mly = Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (y)
in (let mly = (match (add_unit) with
| true -> begin
Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((mly, (Microsoft_FStar_Extraction_ML_Syntax.ml_unit)::[]))
end
| false -> begin
mly
end)
in (let gamma = (Fv ((x, mly, t_x)))::g.gamma
in (let tcenv = (Microsoft_FStar_Tc_Env.push_local_binding g.tcenv (Microsoft_FStar_Tc_Env.Binding_lid ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let _56_200 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _56_200.tydefs; currentModule = _56_200.currentModule})))))
end
| false -> begin
(Support.All.failwith "freevars found")
end))

let extend_fv = (fun ( g ) ( x ) ( t_x ) ( add_unit ) -> (let mlp = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident x.Microsoft_FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit)))

let extend_lb = (fun ( g ) ( l ) ( t ) ( t_x ) ( add_unit ) -> (match (l) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _70_27240 = (extend_bv g (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit)
in (_70_27240, (Microsoft_FStar_Extraction_ML_Syntax.as_mlident x)))
end
| Support.Microsoft.FStar.Util.Inr (f) -> begin
(let _56_218 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_56_218) with
| (p, y) -> begin
(let _70_27242 = (let _70_27241 = (Microsoft_FStar_Absyn_Util.fvvar_of_lid f t)
in (extend_fv' g _70_27241 (p, y) t_x add_unit))
in (_70_27242, (y, 0)))
end))
end))

let extend_tydef = (fun ( g ) ( td ) -> (let m = (Support.List.append (Support.Prims.fst g.currentModule) (((Support.Prims.snd g.currentModule))::[]))
in (let _56_222 = g
in {tcenv = _56_222.tcenv; gamma = _56_222.gamma; tydefs = ((m, td))::g.tydefs; currentModule = _56_222.currentModule})))

let emptyMlPath = ([], "")

let mkContext = (fun ( e ) -> (let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (let a = ("\'a", (- (1)))
in (let failwith_ty = ((a)::[], Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (a))))
in (let _70_27249 = (extend_lb env (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Const.failwith_lid)) Microsoft_FStar_Absyn_Syntax.tun failwith_ty false)
in (Support.All.pipe_right _70_27249 Support.Prims.fst))))))




