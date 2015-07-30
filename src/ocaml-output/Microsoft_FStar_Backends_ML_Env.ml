
type binding =
| Ty of (Microsoft_FStar_Absyn_Syntax.btvar * Microsoft_FStar_Backends_ML_Syntax.mlident * Microsoft_FStar_Backends_ML_Syntax.mlty)
| Bv of (Microsoft_FStar_Absyn_Syntax.bvvar * Microsoft_FStar_Backends_ML_Syntax.mlident * Microsoft_FStar_Backends_ML_Syntax.mltyscheme)
| Fv of (Microsoft_FStar_Absyn_Syntax.fvvar * Microsoft_FStar_Backends_ML_Syntax.mltyscheme)

type env =
{tcenv : Microsoft_FStar_Tc_Env.env; gamma : binding list; tydefs : Microsoft_FStar_Backends_ML_Syntax.mltydecl list; erasableTypes : Microsoft_FStar_Backends_ML_Syntax.mlty  ->  bool; currentModule : Microsoft_FStar_Backends_ML_Syntax.mlpath}

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Set")::[])::(("Map")::[])::(("Heap")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let rec in_ns = (fun ( _51_1 ) -> (match (_51_1) with
| ([], _) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_, _) -> begin
false
end))

let path_of_ns = (fun ( currentModule ) ( ns ) -> (let ns = (Support.List.map (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.idText) ns)
in (let outsupport = (fun ( _51_39 ) -> (match (_51_39) with
| (ns1, ns2) -> begin
if (ns1 = ns2) then begin
[]
end else begin
((Support.String.concat "_" ns2))::[]
end
end))
in (let chkin = (fun ( sns ) -> if (in_ns (sns, ns)) then begin
Some (sns)
end else begin
None
end)
in (match ((Support.List.tryPick chkin outmod)) with
| None -> begin
(match ((Support.List.tryPick chkin (! (Microsoft_FStar_Options.codegen_libs)))) with
| None -> begin
(outsupport ((Support.List.append (Support.Prims.fst currentModule) (((Support.Prims.snd currentModule))::[])), ns))
end
| _ -> begin
ns
end)
end
| Some (sns) -> begin
("Support")::ns
end)))))

let mlpath_of_lident = (fun ( currentModule ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.str) with
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
in ((path_of_ns currentModule ns), x)))
end))

let mkFvvar = (fun ( l ) ( t ) -> {Microsoft_FStar_Absyn_Syntax.v = l; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = (Support.Microsoft.FStar.Range.mk_range "" 0 0)})

let erasedContent = Microsoft_FStar_Backends_ML_Syntax.MLTY_Named (([], (("Support")::("Prims")::[], "unit")))

let ml_unit_ty = erasedContent

let rec erasableType_init = (fun ( t ) -> if (t = ml_unit_ty) then begin
true
end else begin
(match (t) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((_, ("Ghost"::[], "erased"))) -> begin
true
end
| _ -> begin
false
end)
end)

let unknownType = Microsoft_FStar_Backends_ML_Syntax.MLTY_Top

let prependTick = (fun ( _51_78 ) -> (match (_51_78) with
| (x, n) -> begin
if (Support.Microsoft.FStar.Util.starts_with x "\'") then begin
(x, n)
end else begin
((Support.String.strcat "\'" x), n)
end
end))

let convRange = (fun ( r ) -> 0)

let convIdent = (fun ( id ) -> (id.Microsoft_FStar_Absyn_Syntax.idText, (convRange id.Microsoft_FStar_Absyn_Syntax.idRange)))

let btvar_as_mlident = (fun ( btv ) -> (prependTick (convIdent btv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)))

let rec lookup_ty_local = (fun ( gamma ) ( b ) -> (match (gamma) with
| Ty ((bt, mli, mlt))::tl -> begin
if (Microsoft_FStar_Absyn_Util.bvd_eq bt.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v) then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| _::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(failwith (Support.String.strcat "extraction: unbound type var " b.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText))
end))

let lookup_ty_const = (fun ( tydefs ) ( ftv ) -> (failwith "Should not be looking up a constant"))

let lookup_ty = (fun ( g ) ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bt) -> begin
(lookup_ty_local g.gamma bt)
end
| Support.Microsoft.FStar.Util.Inr (ftv) -> begin
(lookup_ty_const g.tydefs ftv)
end))

let lookup_fv = (fun ( g ) ( fv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _51_2 ) -> (match (_51_2) with
| Fv ((fv', sc)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v fv'.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (((mlpath_of_lident g.currentModule fv'.Microsoft_FStar_Absyn_Syntax.v), sc))
end
| _ -> begin
None
end)))
in (match (x) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "(%s) free Variable %s not found\n" (Support.Microsoft.FStar.Range.string_of_range fv.Microsoft_FStar_Absyn_Syntax.p) (Microsoft_FStar_Absyn_Print.sli fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| Some (y) -> begin
y
end)))

let lookup_bv = (fun ( g ) ( bv ) -> (let x = (Support.Microsoft.FStar.Util.find_map g.gamma (fun ( _51_3 ) -> (match (_51_3) with
| Bv ((bv', id, sc)) when (Microsoft_FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc))
end
| _ -> begin
None
end)))
in (match (x) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "(%s) bound Variable %s not found\n" (Support.Microsoft.FStar.Range.string_of_range bv.Microsoft_FStar_Absyn_Syntax.p) (Microsoft_FStar_Absyn_Print.strBvd bv.Microsoft_FStar_Absyn_Syntax.v)))
end
| Some (y) -> begin
y
end)))

let lookup = (fun ( g ) ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let _51_137 = (lookup_bv g x)
in (match (_51_137) with
| (id, t) -> begin
(Microsoft_FStar_Backends_ML_Syntax.MLE_Var (id), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _51_142 = (lookup_fv g x)
in (match (_51_142) with
| (id, t) -> begin
(Microsoft_FStar_Backends_ML_Syntax.MLE_Name (id), t)
end))
end))

let lookup_var = (fun ( g ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
((lookup g (Support.Microsoft.FStar.Util.Inl (x))), false)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((x, b)) -> begin
((lookup g (Support.Microsoft.FStar.Util.Inr (x))), b)
end
| _ -> begin
(failwith "impossible")
end))

let extend_ty = (fun ( g ) ( a ) ( mapped_to ) -> (let ml_a = (btvar_as_mlident a)
in (let mapped_to = (match (mapped_to) with
| None -> begin
Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (let gamma = (Ty ((a, ml_a, mapped_to)))::g.gamma
in (let tcenv = (Microsoft_FStar_Tc_Env.push_local_binding g.tcenv (Microsoft_FStar_Tc_Env.Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, a.Microsoft_FStar_Absyn_Syntax.sort))))
in (let _51_163 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _51_163.tydefs; erasableTypes = _51_163.erasableTypes; currentModule = _51_163.currentModule}))))))

let extend_bv = (fun ( g ) ( x ) ( t_x ) -> (let gamma = (Bv ((x, (Microsoft_FStar_Backends_ML_Syntax.as_mlident x.Microsoft_FStar_Absyn_Syntax.v), t_x)))::g.gamma
in (let tcenv = (Microsoft_FStar_Tc_Env.push_local_binding g.tcenv (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let _51_170 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _51_170.tydefs; erasableTypes = _51_170.erasableTypes; currentModule = _51_170.currentModule}))))

let rec mltyFvars = (fun ( t ) -> (match (t) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, f, t2)) -> begin
(Support.List.append (mltyFvars t1) (mltyFvars t2))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, path)) -> begin
(Support.List.collect mltyFvars args)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (ts) -> begin
(Support.List.collect mltyFvars ts)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(Support.List.append (mltyFvars t1) (mltyFvars t2))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
[]
end))

let rec subsetMlidents = (fun ( la ) ( lb ) -> (match (la) with
| h::tla -> begin
((Support.List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

let tySchemeIsClosed = (fun ( tys ) -> (subsetMlidents (mltyFvars (Support.Prims.snd tys)) (Support.Prims.fst tys)))

let extend_fv' = (fun ( g ) ( x ) ( t_x ) -> if (tySchemeIsClosed t_x) then begin
(let gamma = (Fv ((x, t_x)))::g.gamma
in (let tcenv = (Microsoft_FStar_Tc_Env.push_local_binding g.tcenv (Microsoft_FStar_Tc_Env.Binding_lid ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let _51_203 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _51_203.tydefs; erasableTypes = _51_203.erasableTypes; currentModule = _51_203.currentModule})))
end else begin
(failwith "freevars found")
end)

let extend_fv = (fun ( g ) ( x ) ( t_x ) -> (extend_fv' g x t_x))

let extend_lb = (fun ( g ) ( l ) ( t ) ( t_x ) -> (match (l) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
((extend_bv g (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t) t_x), (Microsoft_FStar_Backends_ML_Syntax.as_mlident x))
end
| Support.Microsoft.FStar.Util.Inr (f) -> begin
(let _51_219 = (mlpath_of_lident g.currentModule f)
in (match (_51_219) with
| (_, y) -> begin
((extend_fv' g (Microsoft_FStar_Absyn_Util.fvvar_of_lid f t) t_x), (y, 0))
end))
end))

let extend_tydef = (fun ( g ) ( td ) -> (let _51_222 = g
in {tcenv = _51_222.tcenv; gamma = _51_222.gamma; tydefs = (td)::g.tydefs; erasableTypes = _51_222.erasableTypes; currentModule = _51_222.currentModule}))

let erasableType = (fun ( g ) ( t ) -> (g.erasableTypes t))




