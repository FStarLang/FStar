
open Prims
# 25 "FStar.Extraction.ML.Env.fst"
type binding =
| Ty of (FStar_Absyn_Syntax.btvar * FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
| Bv of (FStar_Absyn_Syntax.bvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)
| Fv of (FStar_Absyn_Syntax.fvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)

# 28 "FStar.Extraction.ML.Env.fst"
let is_Ty = (fun _discr_ -> (match (_discr_) with
| Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Extraction.ML.Env.fst"
let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Extraction.ML.Env.fst"
let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Extraction.ML.Env.fst"
let ___Ty____0 = (fun projectee -> (match (projectee) with
| Ty (_71_6) -> begin
_71_6
end))

# 29 "FStar.Extraction.ML.Env.fst"
let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_71_9) -> begin
_71_9
end))

# 30 "FStar.Extraction.ML.Env.fst"
let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_71_12) -> begin
_71_12
end))

# 30 "FStar.Extraction.ML.Env.fst"
type env =
{tcenv : FStar_Tc_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}

# 32 "FStar.Extraction.ML.Env.fst"
let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 39 "FStar.Extraction.ML.Env.fst"
let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> if (FStar_Options.debug_at_level (Prims.snd g.currentModule) (FStar_Options.Other ("Extraction"))) then begin
(f ())
end else begin
()
end)

# 43 "FStar.Extraction.ML.Env.fst"
let mkFvvar : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Ident.lident, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l t -> (let _164_69 = (FStar_Range.mk_range "" 0 0)
in {FStar_Absyn_Syntax.v = l; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _164_69}))

# 49 "FStar.Extraction.ML.Env.fst"
let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty

# 53 "FStar.Extraction.ML.Env.fst"
let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_71_24, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| _71_33 -> begin
false
end)
end)

# 59 "FStar.Extraction.ML.Env.fst"
let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top

# 62 "FStar.Extraction.ML.Env.fst"
let prependTick = (fun _71_36 -> (match (_71_36) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
((x), (n))
end else begin
(((Prims.strcat "\'A" x)), (n))
end
end))

# 65 "FStar.Extraction.ML.Env.fst"
let removeTick = (fun _71_39 -> (match (_71_39) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _164_74 = (FStar_Util.substring_from x 1)
in ((_164_74), (n)))
end else begin
((x), (n))
end
end))

# 66 "FStar.Extraction.ML.Env.fst"
let convRange : FStar_Range.range  ->  Prims.int = (fun r -> 0)

# 68 "FStar.Extraction.ML.Env.fst"
let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> ((id.FStar_Ident.idText), ((convRange id.FStar_Ident.idRange))))

# 69 "FStar.Extraction.ML.Env.fst"
let btvar_as_mltyvar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (prependTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

# 84 "FStar.Extraction.ML.Env.fst"
let btvar_as_mlTermVar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (removeTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

# 86 "FStar.Extraction.ML.Env.fst"
let rec lookup_ty_local : binding Prims.list  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Ty (bt, mli, mlt))::tl -> begin
if (FStar_Absyn_Util.bvd_eq bt.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| (_71_55)::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText))
end))

# 92 "FStar.Extraction.ML.Env.fst"
let tyscheme_of_td = (fun _71_62 -> (match (_71_62) with
| (_71_59, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| _71_67 -> begin
None
end)
end))

# 96 "FStar.Extraction.ML.Env.fst"
let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _71_71 -> (match (_71_71) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _71_74 -> (match (_71_74) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (
# 103 "FStar.Extraction.ML.Env.fst"
let _71_81 = td
in (match (_71_81) with
| (n, _71_78, _71_80) -> begin
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

# 107 "FStar.Extraction.ML.Env.fst"
let lookup_tyvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))

# 109 "FStar.Extraction.ML.Env.fst"
let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (
# 112 "FStar.Extraction.ML.Env.fst"
let x = (FStar_Util.find_map g.gamma (fun _71_1 -> (match (_71_1) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv fv'.FStar_Absyn_Syntax.v) -> begin
Some (((path), (sc), (b)))
end
| _71_94 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _164_104 = (let _164_103 = (FStar_Absyn_Print.sli fv)
in (FStar_Util.format1 "free Variable %s not found\n" _164_103))
in (FStar_All.failwith _164_104))
end
| Some (y) -> begin
y
end)))

# 117 "FStar.Extraction.ML.Env.fst"
let lookup_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (
# 121 "FStar.Extraction.ML.Env.fst"
let x = (FStar_Util.find_map g.gamma (fun _71_2 -> (match (_71_2) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v fv'.FStar_Absyn_Syntax.v) -> begin
Some (((path), (sc), (b)))
end
| _71_109 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _164_112 = (let _164_111 = (FStar_Range.string_of_range fv.FStar_Absyn_Syntax.p)
in (let _164_110 = (FStar_Absyn_Print.sli fv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _164_111 _164_110)))
in (FStar_All.failwith _164_112))
end
| Some (y) -> begin
y
end)))

# 126 "FStar.Extraction.ML.Env.fst"
let lookup_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g bv -> (
# 129 "FStar.Extraction.ML.Env.fst"
let x = (FStar_Util.find_map g.gamma (fun _71_3 -> (match (_71_3) with
| Bv (bv', id, sc, f) when (FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some (((id), (sc), (f)))
end
| _71_124 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _164_120 = (let _164_119 = (FStar_Range.string_of_range bv.FStar_Absyn_Syntax.p)
in (let _164_118 = (FStar_Absyn_Print.strBvd bv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _164_119 _164_118)))
in (FStar_All.failwith _164_120))
end
| Some (y) -> begin
y
end)))

# 134 "FStar.Extraction.ML.Env.fst"
let lookup : env  ->  (FStar_Absyn_Syntax.bvvar, FStar_Absyn_Syntax.fvvar) FStar_Util.either  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(lookup_bv g x)
end
| FStar_Util.Inr (x) -> begin
(lookup_fv g x)
end))

# 140 "FStar.Extraction.ML.Env.fst"
let lookup_var = (fun g e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _164_127 = (lookup g (FStar_Util.Inl (x)))
in ((_164_127), (None)))
end
| FStar_Absyn_Syntax.Exp_fvar (x, b) -> begin
(let _164_128 = (lookup g (FStar_Util.Inr (x)))
in ((_164_128), (b)))
end
| _71_144 -> begin
(FStar_All.failwith "impossible")
end))

# 145 "FStar.Extraction.ML.Env.fst"
let extend_ty : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (
# 157 "FStar.Extraction.ML.Env.fst"
let ml_a = (btvar_as_mltyvar a)
in (
# 158 "FStar.Extraction.ML.Env.fst"
let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (
# 161 "FStar.Extraction.ML.Env.fst"
let gamma = (Ty (((a), (ml_a), (mapped_to))))::g.gamma
in (
# 162 "FStar.Extraction.ML.Env.fst"
let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_typ (((a.FStar_Absyn_Syntax.v), (a.FStar_Absyn_Syntax.sort)))))
in (
# 163 "FStar.Extraction.ML.Env.fst"
let _71_155 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _71_155.tydefs; currentModule = _71_155.currentModule}))))))

# 163 "FStar.Extraction.ML.Env.fst"
let extend_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (
# 166 "FStar.Extraction.ML.Env.fst"
let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _71_167 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (
# 169 "FStar.Extraction.ML.Env.fst"
let mlx = FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))
in (
# 170 "FStar.Extraction.ML.Env.fst"
let mlx = if mk_unit then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end
end
in (
# 175 "FStar.Extraction.ML.Env.fst"
let gamma = (Bv (((x), (mlx), (t_x), (is_rec))))::g.gamma
in (
# 176 "FStar.Extraction.ML.Env.fst"
let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))))
in (
# 177 "FStar.Extraction.ML.Env.fst"
let _71_173 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _71_173.tydefs; currentModule = _71_173.currentModule})))))))

# 177 "FStar.Extraction.ML.Env.fst"
let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _164_150 = (mltyFvars t1)
in (let _164_149 = (mltyFvars t2)
in (FStar_List.append _164_150 _164_149)))
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

# 185 "FStar.Extraction.ML.Env.fst"
let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| (h)::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

# 190 "FStar.Extraction.ML.Env.fst"
let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _164_157 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _164_157 (Prims.fst tys))))

# 193 "FStar.Extraction.ML.Env.fst"
let extend_fv' : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(
# 198 "FStar.Extraction.ML.Env.fst"
let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _71_207 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (
# 201 "FStar.Extraction.ML.Env.fst"
let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (
# 202 "FStar.Extraction.ML.Env.fst"
let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (
# 203 "FStar.Extraction.ML.Env.fst"
let gamma = (Fv (((x), (mly), (t_x), (is_rec))))::g.gamma
in (
# 204 "FStar.Extraction.ML.Env.fst"
let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_lid (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))))
in (
# 205 "FStar.Extraction.ML.Env.fst"
let _71_213 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _71_213.tydefs; currentModule = _71_213.currentModule}))))))
end else begin
(FStar_All.failwith "freevars found")
end)

# 207 "FStar.Extraction.ML.Env.fst"
let extend_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (
# 210 "FStar.Extraction.ML.Env.fst"
let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))

# 215 "FStar.Extraction.ML.Env.fst"
let extend_lb : env  ->  FStar_Absyn_Syntax.lbname  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _164_192 = (extend_bv g (FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit is_rec false)
in ((_164_192), ((FStar_Extraction_ML_Syntax.as_mlident x))))
end
| FStar_Util.Inr (f) -> begin
(
# 222 "FStar.Extraction.ML.Env.fst"
let _71_233 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_71_233) with
| (p, y) -> begin
(let _164_193 = (extend_fv' g (FStar_Absyn_Util.fvvar_of_lid f t) ((p), (y)) t_x add_unit is_rec)
in ((_164_193), (((y), (0)))))
end))
end))

# 223 "FStar.Extraction.ML.Env.fst"
let extend_tydef : env  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g td -> (
# 226 "FStar.Extraction.ML.Env.fst"
let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (
# 227 "FStar.Extraction.ML.Env.fst"
let _71_237 = g
in {tcenv = _71_237.tcenv; gamma = _71_237.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = _71_237.currentModule})))

# 227 "FStar.Extraction.ML.Env.fst"
let emptyMlPath : (Prims.string Prims.list * Prims.string) = (([]), (""))

# 230 "FStar.Extraction.ML.Env.fst"
let mkContext : FStar_Tc_Env.env  ->  env = (fun e -> (
# 233 "FStar.Extraction.ML.Env.fst"
let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (
# 234 "FStar.Extraction.ML.Env.fst"
let a = (("\'a"), ((- (1))))
in (
# 235 "FStar.Extraction.ML.Env.fst"
let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (let _164_200 = (extend_lb env (FStar_Util.Inr (FStar_Absyn_Const.failwith_lid)) FStar_Absyn_Syntax.tun failwith_ty false false)
in (FStar_All.pipe_right _164_200 Prims.fst))))))




