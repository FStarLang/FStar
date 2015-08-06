
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

type env =
{tcenv : Microsoft_FStar_Tc_Env.env; gamma : binding list; tydefs : (Microsoft_FStar_Extraction_ML_Syntax.mlsymbol list * Microsoft_FStar_Extraction_ML_Syntax.mltydecl) list; currentModule : Microsoft_FStar_Extraction_ML_Syntax.mlpath}

let is_Mkenv = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv"))

let debug = (fun ( g ) ( f ) -> (match ((((Support.ST.read Microsoft_FStar_Options.debug) <> []) && ((let _70_24239 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.List.contains "Prims" _70_24239)) || (g.currentModule <> ([], "Prims"))))) with
| true -> begin
(f ())
end
| false -> begin
()
end))

let mkFvvar = (fun ( l ) ( t ) -> (let _70_24244 = (Support.Microsoft.FStar.Range.mk_range "" 0 0)
in {Microsoft_FStar_Absyn_Syntax.v = l; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _70_24244}))

let erasedContent = Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty

let erasableTypeNoDelta = (fun ( t ) -> (match (t) with
| _56_21 -> begin
(match ((t = Microsoft_FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| false -> begin
(match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((_56_23, ("Ghost"::[], "erased"))) -> begin
true
end
| _56_31 -> begin
false
end)
end)
end))

let unknownType = Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top

let prependTick = (fun ( _56_34 ) -> (match (_56_34) with
| (x, n) -> begin
(match ((Support.Microsoft.FStar.Util.starts_with x "\'")) with
| true -> begin
(x, n)
end
| false -> begin
((Support.String.strcat "\' " x), n)
end)
end))

let removeTick = (fun ( _56_37 ) -> (match (_56_37) with
| (x, n) -> begin
(match ((Support.Microsoft.FStar.Util.starts_with x "\'")) with
| true -> begin
(let _70_24249 = (Support.Microsoft.FStar.Util.substring_from x 1)
in (_70_24249, n))
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
| _56_53::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(Support.All.failwith (Support.String.strcat "extraction: unbound type var " b.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText))
end))

let tyscheme_of_td = (fun ( _56_60 ) -> (match (_56_60) with
| (_56_57, vars, body_opt) -> begin
(match (body_opt) with
| Some (Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some ((vars, t))
end
| _56_65 -> begin
None
end)
end))

let lookup_ty_const = (fun ( env ) ( _56_69 ) -> (match (_56_69) with
| (module_name, ty_name) -> begin
(Support.Microsoft.FStar.Util.find_map env.tydefs (fun ( _56_72 ) -> (match (_56_72) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(Support.Microsoft.FStar.Util.find_map tds (fun ( td ) -> (let _56_79 = td
in (match (_56_79) with
| (n, _56_76, _56_78) -> begin
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
| _56_91 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _70_24279 = (let _70_24278 = (Microsoft_FStar_Absyn_Print.sli fv)
in (Support.Microsoft.FStar.Util.format1 "free Variable %s not found\n" _70_24278))
in (Support.All.failwith _70_24279))
end
| Some (y) -> begin
y
end)))

let lookup_fv = (fun ( g ) ( fv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _56_2 ) -> (match (_56_2) with
| Fv ((fv', path, sc)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v fv'.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((path, sc))
end
| _56_105 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _70_24287 = (let _70_24286 = (Support.Microsoft.FStar.Range.string_of_range fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_24285 = (Microsoft_FStar_Absyn_Print.sli fv.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "(%s) free Variable %s not found\n" _70_24286 _70_24285)))
in (Support.All.failwith _70_24287))
end
| Some (y) -> begin
y
end)))

let lookup_bv = (fun ( g ) ( bv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _56_3 ) -> (match (_56_3) with
| Bv ((bv', id, sc)) when (Microsoft_FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc))
end
| _56_119 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _70_24295 = (let _70_24294 = (Support.Microsoft.FStar.Range.string_of_range bv.Microsoft_FStar_Absyn_Syntax.p)
in (let _70_24293 = (Microsoft_FStar_Absyn_Print.strBvd bv.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "(%s) bound Variable %s not found\n" _70_24294 _70_24293)))
in (Support.All.failwith _70_24295))
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
(let _70_24302 = (lookup g (Support.Microsoft.FStar.Util.Inl (x)))
in (_70_24302, None))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, b)) -> begin
(let _70_24303 = (lookup g (Support.Microsoft.FStar.Util.Inr (x)))
in (_70_24303, b))
end
| _56_139 -> begin
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
in (let _56_150 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _56_150.tydefs; currentModule = _56_150.currentModule}))))))

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
in (let _56_160 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _56_160.tydefs; currentModule = _56_160.currentModule}))))))

let rec mltyFvars = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, f, t2)) -> begin
(let _70_24321 = (mltyFvars t1)
in (let _70_24320 = (mltyFvars t2)
in (Support.List.append _70_24321 _70_24320)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, path)) -> begin
(Support.List.collect mltyFvars args)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(Support.List.collect mltyFvars ts)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let _70_24323 = (mltyFvars t1)
in (let _70_24322 = (mltyFvars t2)
in (Support.List.append _70_24323 _70_24322)))
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

let tySchemeIsClosed = (fun ( tys ) -> (let _70_24330 = (mltyFvars (Support.Prims.snd tys))
in (subsetMlidents _70_24330 (Support.Prims.fst tys))))

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
in (let _56_197 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _56_197.tydefs; currentModule = _56_197.currentModule})))))
end
| false -> begin
(Support.All.failwith "freevars found")
end))

let extend_fv = (fun ( g ) ( x ) ( t_x ) ( add_unit ) -> (let mlp = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident x.Microsoft_FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit)))

let extend_lb = (fun ( g ) ( l ) ( t ) ( t_x ) ( add_unit ) -> (match (l) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _70_24359 = (extend_bv g (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit)
in (_70_24359, (Microsoft_FStar_Extraction_ML_Syntax.as_mlident x)))
end
| Support.Microsoft.FStar.Util.Inr (f) -> begin
(let _56_215 = (Microsoft_FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_56_215) with
| (p, y) -> begin
(let _70_24361 = (let _70_24360 = (Microsoft_FStar_Absyn_Util.fvvar_of_lid f t)
in (extend_fv' g _70_24360 (p, y) t_x add_unit))
in (_70_24361, (y, 0)))
end))
end))

let extend_tydef = (fun ( g ) ( td ) -> (let m = (Support.List.append (Support.Prims.fst g.currentModule) (((Support.Prims.snd g.currentModule))::[]))
in (let _56_219 = g
in {tcenv = _56_219.tcenv; gamma = _56_219.gamma; tydefs = ((m, td))::g.tydefs; currentModule = _56_219.currentModule})))

let emptyMlPath = ([], "")

let mkContext = (fun ( e ) -> (let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (let a = ("\'a", (- (1)))
in (let failwith_ty = ((a)::[], Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), Microsoft_FStar_Extraction_ML_Syntax.E_IMPURE, Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (a))))
in (let _70_24368 = (extend_lb env (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Const.failwith_lid)) Microsoft_FStar_Absyn_Syntax.tun failwith_ty false)
in (Support.All.pipe_right _70_24368 Support.Prims.fst))))))




