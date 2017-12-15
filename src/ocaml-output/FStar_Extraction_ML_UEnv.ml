
open Prims
open FStar_Pervasives

type ty_or_exp_b =
((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty), (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)) FStar_Util.either

type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b)


let uu___is_Bv : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bv (_0) -> begin
true
end
| uu____42 -> begin
false
end))


let __proj__Bv__item___0 : binding  ->  (FStar_Syntax_Syntax.bv * ty_or_exp_b) = (fun projectee -> (match (projectee) with
| Bv (_0) -> begin
_0
end))


let uu___is_Fv : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fv (_0) -> begin
true
end
| uu____72 -> begin
false
end))


let __proj__Fv__item___0 : binding  ->  (FStar_Syntax_Syntax.fv * ty_or_exp_b) = (fun projectee -> (match (projectee) with
| Fv (_0) -> begin
_0
end))

type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; type_names : FStar_Syntax_Syntax.fv Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let __proj__Mkenv__item__tcenv : env  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; type_names = __fname__type_names; currentModule = __fname__currentModule} -> begin
__fname__tcenv
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; type_names = __fname__type_names; currentModule = __fname__currentModule} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__tydefs : env  ->  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; type_names = __fname__type_names; currentModule = __fname__currentModule} -> begin
__fname__tydefs
end))


let __proj__Mkenv__item__type_names : env  ->  FStar_Syntax_Syntax.fv Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; type_names = __fname__type_names; currentModule = __fname__currentModule} -> begin
__fname__type_names
end))


let __proj__Mkenv__item__currentModule : env  ->  FStar_Extraction_ML_Syntax.mlpath = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; type_names = __fname__type_names; currentModule = __fname__currentModule} -> begin
__fname__currentModule
end))


let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> (

let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in (

let uu____268 = (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction")))
in (match (uu____268) with
| true -> begin
(f ())
end
| uu____269 -> begin
()
end))))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match ((Prims.op_Equality t FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| uu____282 -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____283, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| uu____296 -> begin
false
end)
end))


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick : Prims.string  ->  Prims.string = (fun x -> (match ((FStar_Util.starts_with x "\'")) with
| true -> begin
x
end
| uu____301 -> begin
(Prims.strcat "\'A" x)
end))


let removeTick : Prims.string  ->  Prims.string = (fun x -> (match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(FStar_Util.substring_from x (Prims.parse_int "1"))
end
| uu____306 -> begin
x
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  FStar_Extraction_ML_Syntax.mlident = (fun id -> id.FStar_Ident.idText)


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let uu____319 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick uu____319)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let uu____324 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick uu____324)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
mlt
end
| uu____371 -> begin
(lookup_ty_local tl1 b)
end)
end
| (Bv (b', FStar_Util.Inr (uu____373)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end
| uu____413 -> begin
(lookup_ty_local tl1 b)
end)
end
| (uu____414)::tl1 -> begin
(lookup_ty_local tl1 b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td : 'Auu____428 'Auu____429 'Auu____430 'Auu____431 . ('Auu____431 * 'Auu____430 * 'Auu____429 * FStar_Extraction_ML_Syntax.mlidents * 'Auu____428 * FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option)  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun uu____451 -> (match (uu____451) with
| (uu____466, uu____467, uu____468, vars, uu____470, body_opt) -> begin
(match (body_opt) with
| FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
FStar_Pervasives_Native.Some (((vars), (t)))
end
| uu____485 -> begin
FStar_Pervasives_Native.None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun env uu____497 -> (match (uu____497) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun uu____517 -> (match (uu____517) with
| (m, tds) -> begin
(match ((Prims.op_Equality module_name m)) with
| true -> begin
(FStar_Util.find_map tds (fun td -> (

let uu____545 = td
in (match (uu____545) with
| (uu____548, n1, uu____550, uu____551, uu____552, uu____553) -> begin
(match ((Prims.op_Equality n1 ty_name)) with
| true -> begin
(tyscheme_of_td td)
end
| uu____566 -> begin
FStar_Pervasives_Native.None
end)
end))))
end
| uu____567 -> begin
FStar_Pervasives_Native.None
end)
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun uu____611 -> (match (uu____611) with
| (m, tds) -> begin
(FStar_Util.find_map tds (fun uu____645 -> (match (uu____645) with
| (uu____654, n1, mangle_opt, uu____657, uu____658, uu____659) -> begin
(match ((Prims.op_Equality m mname)) with
| true -> begin
(match ((Prims.op_Equality n1 ty_name)) with
| true -> begin
(match (mangle_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((m), (n1)))
end
| FStar_Pervasives_Native.Some (mangled) -> begin
(

let modul = m
in FStar_Pervasives_Native.Some (((modul), (mangled))))
end)
end
| uu____714 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____721 -> begin
FStar_Pervasives_Native.None
end)
end)))
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___131_750 -> (match (uu___131_750) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____755 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____756 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (failwith uu____756))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___132_772 -> (match (uu___132_772) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____777 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____778 = (

let uu____779 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (

let uu____780 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" uu____779 uu____780)))
in (failwith uu____778))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___133_796 -> (match (uu___133_796) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____801 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____802 = (

let uu____803 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____804 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____803 uu____804)))
in (failwith uu____802))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let uu____835 = (lookup_bv g x1)
in ((uu____835), (FStar_Pervasives_Native.None)))
end
| FStar_Util.Inr (x1) -> begin
(

let uu____839 = (lookup_fv g x1)
in ((uu____839), (x1.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____864 -> begin
(failwith "Impossible: lookup_term for a non-name")
end))


let extend_ty : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option  ->  env = (fun g a mapped_to -> (

let ml_a = (bv_as_ml_tyvar a)
in (

let mapped_to1 = (match (mapped_to) with
| FStar_Pervasives_Native.None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end)
in (

let gamma = (Bv (((a), (FStar_Util.Inl (((ml_a), (mapped_to1)))))))::g.gamma
in (

let tcenv = (FStar_TypeChecker_Env.push_bv g.tcenv a)
in (

let uu___135_922 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___135_922.tydefs; type_names = uu___135_922.type_names; currentModule = uu___135_922.currentModule}))))))


let sanitize : Prims.string  ->  Prims.string = (fun s -> (

let cs = (FStar_String.list_of_string s)
in (

let valid = (fun c -> (((FStar_Util.is_letter_or_digit c) || (Prims.op_Equality c 95 (*_*))) || (Prims.op_Equality c 39 (*'*))))
in (

let cs' = (FStar_List.fold_right (fun c cs1 -> (

let uu____946 = (

let uu____949 = (valid c)
in (match (uu____949) with
| true -> begin
(c)::[]
end
| uu____952 -> begin
(95 (*_*))::(95 (*_*))::[]
end))
in (FStar_List.append uu____946 cs1))) cs [])
in (

let cs'1 = (match (cs') with
| (c)::cs1 when ((FStar_Util.is_digit c) || (Prims.op_Equality c 39 (*'*))) -> begin
(95 (*_*))::(c)::cs1
end
| uu____962 -> begin
cs
end)
in (FStar_String.string_of_list cs'1))))))


let find_uniq : binding Prims.list  ->  Prims.string  ->  Prims.string = (fun gamma mlident -> (

let rec find_uniq = (fun mlident1 i -> (

let suffix = (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
""
end
| uu____985 -> begin
(FStar_Util.string_of_int i)
end)
in (

let target_mlident = (Prims.strcat mlident1 suffix)
in (

let has_collision = (FStar_List.existsb (fun uu___134_992 -> (match (uu___134_992) with
| Bv (uu____993, FStar_Util.Inl (mlident', uu____995)) -> begin
(Prims.op_Equality target_mlident mlident')
end
| Fv (uu____1024, FStar_Util.Inl (mlident', uu____1026)) -> begin
(Prims.op_Equality target_mlident mlident')
end
| Fv (uu____1055, FStar_Util.Inr (mlident', uu____1057, uu____1058, uu____1059)) -> begin
(Prims.op_Equality target_mlident mlident')
end
| Bv (uu____1088, FStar_Util.Inr (mlident', uu____1090, uu____1091, uu____1092)) -> begin
(Prims.op_Equality target_mlident mlident')
end)) gamma)
in (match (has_collision) with
| true -> begin
(find_uniq mlident1 (i + (Prims.parse_int "1")))
end
| uu____1121 -> begin
target_mlident
end)))))
in (

let mlident1 = (sanitize mlident)
in (find_uniq mlident1 (Prims.parse_int "0")))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____1159 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mlident = (

let uu____1161 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (find_uniq g.gamma uu____1161))
in (

let mlx = FStar_Extraction_ML_Syntax.MLE_Var (mlident)
in (

let mlx1 = (match (mk_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1164 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____1167 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let t_x1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.pop_unit t_x)
end
| uu____1169 -> begin
t_x
end)
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlident), (mlx1), (t_x1), (is_rec)))))))::g.gamma
in (

let tcenv = (

let uu____1202 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____1202))
in (((

let uu___136_1204 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___136_1204.tydefs; type_names = uu___136_1204.type_names; currentModule = uu___136_1204.currentModule})), (mlident))))))))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____1217 = (mltyFvars t1)
in (

let uu____1220 = (mltyFvars t2)
in (FStar_List.append uu____1217 uu____1220)))
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


let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (

let uu____1256 = (mltyFvars (FStar_Pervasives_Native.snd tys))
in (subsetMlidents uu____1256 (FStar_Pervasives_Native.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x y t_x add_unit is_rec -> (

let uu____1291 = (tySchemeIsClosed t_x)
in (match (uu____1291) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____1300 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____1301 = (

let uu____1312 = y
in (match (uu____1312) with
| (ns, i) -> begin
(

let mlsymbol = (FStar_Extraction_ML_Syntax.avoid_keyword i)
in ((((ns), (mlsymbol))), (mlsymbol)))
end))
in (match (uu____1301) with
| (mlpath, mlsymbol) -> begin
(

let mly = FStar_Extraction_ML_Syntax.MLE_Name (mlpath)
in (

let mly1 = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____1360 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let t_x1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.pop_unit t_x)
end
| uu____1362 -> begin
t_x
end)
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mlsymbol), (mly1), (t_x1), (is_rec)))))))::g.gamma
in (((

let uu___137_1395 = g
in {tcenv = uu___137_1395.tcenv; gamma = gamma; tydefs = uu___137_1395.tydefs; type_names = uu___137_1395.type_names; currentModule = uu___137_1395.currentModule})), (mlsymbol))))))
end)))
end
| uu____1396 -> begin
(failwith "freevars found")
end)))


let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(extend_bv g x t_x add_unit is_rec false)
end
| FStar_Util.Inr (f) -> begin
(

let uu____1464 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1464) with
| (p, y) -> begin
(extend_fv' g f ((p), (y)) t_x add_unit is_rec)
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu___138_1492 = g
in {tcenv = uu___138_1492.tcenv; gamma = uu___138_1492.gamma; tydefs = (((m), (td)))::g.tydefs; type_names = (fv)::g.type_names; currentModule = uu___138_1492.currentModule})))


let extend_type_name : env  ->  FStar_Syntax_Syntax.fv  ->  env = (fun g fv -> (

let uu___139_1509 = g
in {tcenv = uu___139_1509.tcenv; gamma = uu___139_1509.gamma; tydefs = uu___139_1509.tydefs; type_names = (fv)::g.type_names; currentModule = uu___139_1509.currentModule}))


let is_type_name : env  ->  FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun g fv -> (FStar_All.pipe_right g.type_names (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))))


let emptyMlPath : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; type_names = []; currentModule = emptyMlPath}
in (

let a = "\'a"
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____1559 = (

let uu____1564 = (

let uu____1565 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____1565))
in (extend_lb env uu____1564 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right uu____1559 FStar_Pervasives_Native.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let lid = (FStar_Syntax_Util.mk_field_projector_name_from_ident ed.FStar_Syntax_Syntax.mname (FStar_Ident.id_of_text nm))
in (

let uu____1583 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1583), (lid)))))


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed a -> (

let nm = a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let module_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns
in (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append module_name (((FStar_Ident.id_of_text nm))::[])))
in (

let uu____1601 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1601), (lid)))))))




