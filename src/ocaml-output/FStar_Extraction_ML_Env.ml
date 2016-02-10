
open Prims
# 27 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

type binding =
| Ty of (FStar_Absyn_Syntax.btvar * FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
| Bv of (FStar_Absyn_Syntax.bvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)
| Fv of (FStar_Absyn_Syntax.fvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)

# 28 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let is_Ty = (fun _discr_ -> (match (_discr_) with
| Ty (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let ___Ty____0 : binding  ->  (FStar_Absyn_Syntax.btvar * FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) = (fun projectee -> (match (projectee) with
| Ty (_74_6) -> begin
_74_6
end))

# 29 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let ___Bv____0 : binding  ->  (FStar_Absyn_Syntax.bvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun projectee -> (match (projectee) with
| Bv (_74_9) -> begin
_74_9
end))

# 30 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let ___Fv____0 : binding  ->  (FStar_Absyn_Syntax.fvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun projectee -> (match (projectee) with
| Fv (_74_12) -> begin
_74_12
end))

# 32 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

type env =
{tcenv : FStar_Tc_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}

# 32 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

# 41 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> if (((FStar_ST.read FStar_Options.debug) <> []) && ((let _176_65 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.contains "Prims" _176_65)) || (g.currentModule <> ([], "Prims")))) then begin
(f ())
end else begin
()
end)

# 47 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let mkFvvar : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Ident.lident, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l t -> (let _176_70 = (FStar_Range.mk_range "" 0 0)
in {FStar_Absyn_Syntax.v = l; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _176_70}))

# 55 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty

# 57 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_74_24, ("FStar"::"Ghost"::[], "erased")) -> begin
true
end
| _74_33 -> begin
false
end)
end)

# 64 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top

# 67 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let prependTick = (fun _74_36 -> (match (_74_36) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(x, n)
end else begin
((Prims.strcat "\'A" x), n)
end
end))

# 68 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let removeTick = (fun _74_39 -> (match (_74_39) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _176_75 = (FStar_Util.substring_from x 1)
in (_176_75, n))
end else begin
(x, n)
end
end))

# 70 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let convRange : FStar_Range.range  ->  Prims.int = (fun r -> 0)

# 71 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> (id.FStar_Ident.idText, (convRange id.FStar_Ident.idRange)))

# 86 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let btvar_as_mltyvar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (prependTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

# 88 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let btvar_as_mlTermVar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (removeTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))

# 90 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let rec lookup_ty_local : binding Prims.list  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| Ty (bt, mli, mlt)::tl -> begin
if (FStar_Absyn_Util.bvd_eq bt.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| _74_55::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText))
end))

# 96 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let tyscheme_of_td = (fun _74_62 -> (match (_74_62) with
| (_74_59, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some ((vars, t))
end
| _74_67 -> begin
None
end)
end))

# 101 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _74_71 -> (match (_74_71) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _74_74 -> (match (_74_74) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (let _74_81 = td
in (match (_74_81) with
| (n, _74_78, _74_80) -> begin
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

# 111 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup_tyvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))

# 113 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (let x = (FStar_Util.find_map g.gamma (fun _74_1 -> (match (_74_1) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc, b))
end
| _74_94 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _176_105 = (let _176_104 = (FStar_Absyn_Print.sli fv)
in (FStar_Util.format1 "free Variable %s not found\n" _176_104))
in (FStar_All.failwith _176_105))
end
| Some (y) -> begin
y
end)))

# 122 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (let x = (FStar_Util.find_map g.gamma (fun _74_2 -> (match (_74_2) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v fv'.FStar_Absyn_Syntax.v) -> begin
Some ((path, sc, b))
end
| _74_109 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _176_113 = (let _176_112 = (FStar_Range.string_of_range fv.FStar_Absyn_Syntax.p)
in (let _176_111 = (FStar_Absyn_Print.sli fv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _176_112 _176_111)))
in (FStar_All.failwith _176_113))
end
| Some (y) -> begin
y
end)))

# 130 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g bv -> (let x = (FStar_Util.find_map g.gamma (fun _74_3 -> (match (_74_3) with
| Bv (bv', id, sc, f) when (FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some ((id, sc, f))
end
| _74_124 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _176_121 = (let _176_120 = (FStar_Range.string_of_range bv.FStar_Absyn_Syntax.p)
in (let _176_119 = (FStar_Absyn_Print.strBvd bv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _176_120 _176_119)))
in (FStar_All.failwith _176_121))
end
| Some (y) -> begin
y
end)))

# 139 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup : env  ->  (FStar_Absyn_Syntax.bvvar, FStar_Absyn_Syntax.fvvar) FStar_Util.either  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(lookup_bv g x)
end
| FStar_Util.Inr (x) -> begin
(lookup_fv g x)
end))

# 144 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let lookup_var = (fun g e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _176_128 = (lookup g (FStar_Util.Inl (x)))
in (_176_128, None))
end
| FStar_Absyn_Syntax.Exp_fvar (x, b) -> begin
(let _176_129 = (lookup g (FStar_Util.Inr (x)))
in (_176_129, b))
end
| _74_144 -> begin
(FStar_All.failwith "impossible")
end))

# 158 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let extend_ty : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (let ml_a = (btvar_as_mltyvar a)
in (let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (let gamma = (Ty ((a, ml_a, mapped_to)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))))
in (let _74_155 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _74_155.tydefs; currentModule = _74_155.currentModule}))))))

# 167 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let extend_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _74_167 -> begin
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
in (let gamma = (Bv ((x, mlx, t_x, is_rec)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let _74_173 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _74_173.tydefs; currentModule = _74_173.currentModule})))))))

# 181 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _176_151 = (mltyFvars t1)
in (let _176_150 = (mltyFvars t2)
in (FStar_List.append _176_151 _176_150)))
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

# 189 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| h::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))

# 194 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _176_158 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _176_158 (Prims.fst tys))))

# 197 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let extend_fv' : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _74_207 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly), (FStar_Extraction_ML_Syntax.ml_unit)::[]))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (let gamma = (Fv ((x, mly, t_x, is_rec)))::g.gamma
in (let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_lid ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let _74_213 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _74_213.tydefs; currentModule = _74_213.currentModule}))))))
end else begin
(FStar_All.failwith "freevars found")
end)

# 211 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let extend_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))

# 219 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let extend_lb : env  ->  FStar_Absyn_Syntax.lbname  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _176_193 = (extend_bv g (FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit is_rec false)
in (_176_193, (FStar_Extraction_ML_Syntax.as_mlident x)))
end
| FStar_Util.Inr (f) -> begin
(let _74_233 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_74_233) with
| (p, y) -> begin
(let _176_194 = (extend_fv' g (FStar_Absyn_Util.fvvar_of_lid f t) (p, y) t_x add_unit is_rec)
in (_176_194, (y, 0)))
end))
end))

# 227 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let extend_tydef : env  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g td -> (let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (let _74_237 = g
in {tcenv = _74_237.tcenv; gamma = _74_237.gamma; tydefs = ((m, td))::g.tydefs; currentModule = _74_237.currentModule})))

# 232 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let emptyMlPath : (Prims.string Prims.list * Prims.string) = ([], "")

# 234 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\extraction\\env.fs"

let mkContext : FStar_Tc_Env.env  ->  env = (fun e -> (let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (let a = ("\'a", (- (1)))
in (let failwith_ty = ((a)::[], FStar_Extraction_ML_Syntax.MLTY_Fun ((FStar_Extraction_ML_Syntax.MLTY_Named (([], (("Prims")::[], "string"))), FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.MLTY_Var (a))))
in (let _176_201 = (extend_lb env (FStar_Util.Inr (FStar_Absyn_Const.failwith_lid)) FStar_Absyn_Syntax.tun failwith_ty false false)
in (FStar_All.pipe_right _176_201 Prims.fst))))))




