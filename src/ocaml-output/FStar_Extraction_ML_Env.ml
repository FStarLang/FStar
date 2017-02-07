
open Prims

type binding =
| Ty of (FStar_Absyn_Syntax.btvar * FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
| Bv of (FStar_Absyn_Syntax.bvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)
| Fv of (FStar_Absyn_Syntax.fvvar * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)


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
| Ty (_75_6) -> begin
_75_6
end))


let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_75_9) -> begin
_75_9
end))


let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_75_12) -> begin
_75_12
end))


type env =
{tcenv : FStar_Tc_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> if (FStar_Options.debug_at_level (Prims.snd g.currentModule) (FStar_Options.Other ("Extraction"))) then begin
(f ())
end else begin
()
end)


let mkFvvar : FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Ident.lident, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l t -> (let _174_69 = (FStar_Range.mk_range "" FStar_Range.zeroPos FStar_Range.zeroPos)
in {FStar_Absyn_Syntax.v = l; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _174_69}))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_75_24, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| _75_33 -> begin
false
end)
end)


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick = (fun _75_36 -> (match (_75_36) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
((x), (n))
end else begin
(((Prims.strcat "\'A" x)), (n))
end
end))


let removeTick = (fun _75_39 -> (match (_75_39) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _174_74 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((_174_74), (n)))
end else begin
((x), (n))
end
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> ((id.FStar_Ident.idText), ((convRange id.FStar_Ident.idRange))))


let btvar_as_mltyvar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (prependTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))


let btvar_as_mlTermVar : FStar_Absyn_Syntax.btvar  ->  (Prims.string * Prims.int) = (fun btv -> (removeTick (convIdent btv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Ty (bt, mli, mlt))::tl -> begin
if (FStar_Absyn_Util.bvd_eq bt.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| (_75_55)::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td = (fun _75_66 -> (match (_75_66) with
| (_75_59, _75_61, _75_63, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| _75_71 -> begin
None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _75_75 -> (match (_75_75) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _75_78 -> (match (_75_78) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (

let _75_89 = td
in (match (_75_89) with
| (_75_81, n, _75_84, _75_86, _75_88) -> begin
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


let lookup_tyvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun _75_1 -> (match (_75_1) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv fv'.FStar_Absyn_Syntax.v) -> begin
Some (((path), (sc), (b)))
end
| _75_102 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _174_104 = (let _174_103 = (FStar_Absyn_Print.sli fv)
in (FStar_Util.format1 "free Variable %s not found\n" _174_103))
in (failwith _174_104))
end
| Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun _75_2 -> (match (_75_2) with
| Fv (fv', path, sc, b) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v fv'.FStar_Absyn_Syntax.v) -> begin
Some (((path), (sc), (b)))
end
| _75_117 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _174_112 = (let _174_111 = (FStar_Range.string_of_range fv.FStar_Absyn_Syntax.p)
in (let _174_110 = (FStar_Absyn_Print.sli fv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _174_111 _174_110)))
in (failwith _174_112))
end
| Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun _75_3 -> (match (_75_3) with
| Bv (bv', id, sc, f) when (FStar_Absyn_Util.bvar_eq bv bv') -> begin
Some (((id), (sc), (f)))
end
| _75_132 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _174_120 = (let _174_119 = (FStar_Range.string_of_range bv.FStar_Absyn_Syntax.p)
in (let _174_118 = (FStar_Absyn_Print.strBvd bv.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _174_119 _174_118)))
in (failwith _174_120))
end
| Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Absyn_Syntax.bvvar, FStar_Absyn_Syntax.fvvar) FStar_Util.either  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(lookup_bv g x)
end
| FStar_Util.Inr (x) -> begin
(lookup_fv g x)
end))


let lookup_var = (fun g e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let _174_127 = (lookup g (FStar_Util.Inl (x)))
in ((_174_127), (None)))
end
| FStar_Absyn_Syntax.Exp_fvar (x, b) -> begin
(let _174_128 = (lookup g (FStar_Util.Inr (x)))
in ((_174_128), (b)))
end
| _75_152 -> begin
(failwith "impossible")
end))


let extend_ty : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (

let ml_a = (btvar_as_mltyvar a)
in (

let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (

let gamma = (Ty (((a), (ml_a), (mapped_to))))::g.gamma
in (

let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_typ (((a.FStar_Absyn_Syntax.v), (a.FStar_Absyn_Syntax.sort)))))
in (

let _75_163 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _75_163.tydefs; currentModule = _75_163.currentModule}))))))


let extend_bv : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _75_175 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mlx = FStar_Extraction_ML_Syntax.MLE_Var ((FStar_Extraction_ML_Syntax.as_mlident x.FStar_Absyn_Syntax.v))
in (

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

let gamma = (Bv (((x), (mlx), (t_x), (is_rec))))::g.gamma
in (

let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))))
in (

let _75_181 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _75_181.tydefs; currentModule = _75_181.currentModule})))))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _174_150 = (mltyFvars t1)
in (let _174_149 = (mltyFvars t2)
in (FStar_List.append _174_150 _174_149)))
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


let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| (h)::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))


let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _174_157 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _174_157 (Prims.fst tys))))


let extend_fv' : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _75_215 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mly = FStar_Extraction_ML_Syntax.MLE_Name (y)
in (

let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (

let gamma = (Fv (((x), (mly), (t_x), (is_rec))))::g.gamma
in (

let tcenv = (FStar_Tc_Env.push_local_binding g.tcenv (FStar_Tc_Env.Binding_lid (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))))
in (

let _75_221 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _75_221.tydefs; currentModule = _75_221.currentModule}))))))
end else begin
(failwith "freevars found")
end)


let extend_fv : env  ->  FStar_Absyn_Syntax.fvvar  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Absyn_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Absyn_Syntax.lbname  ->  FStar_Absyn_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _174_192 = (extend_bv g (FStar_Absyn_Util.bvd_to_bvar_s x t) t_x add_unit is_rec false)
in ((_174_192), ((FStar_Extraction_ML_Syntax.as_mlident x))))
end
| FStar_Util.Inr (f) -> begin
(

let _75_241 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f)
in (match (_75_241) with
| (p, y) -> begin
(let _174_193 = (extend_fv' g (FStar_Absyn_Util.fvvar_of_lid f t) ((p), (y)) t_x add_unit is_rec)
in ((_174_193), (((y), ((Prims.parse_int "0"))))))
end))
end))


let extend_tydef : env  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g td -> (

let m = (FStar_List.append (Prims.fst g.currentModule) (((Prims.snd g.currentModule))::[]))
in (

let _75_245 = g
in {tcenv = _75_245.tcenv; gamma = _75_245.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = _75_245.currentModule})))


let emptyMlPath : (Prims.string Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_Tc_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (let _174_200 = (extend_lb env (FStar_Util.Inr (FStar_Absyn_Const.failwith_lid)) FStar_Absyn_Syntax.tun failwith_ty false false)
in (FStar_All.pipe_right _174_200 Prims.fst))))))




