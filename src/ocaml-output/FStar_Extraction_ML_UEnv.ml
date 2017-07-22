
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


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match ((t = FStar_Extraction_ML_Syntax.ml_unit_ty)) with
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


let prependTick : 'Auu____301 . (Prims.string * 'Auu____301)  ->  (Prims.string * 'Auu____301) = (fun uu____313 -> (match (uu____313) with
| (x, n1) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
((x), (n1))
end
| uu____324 -> begin
(((Prims.strcat "\'A" x)), (n1))
end)
end))


let removeTick : 'Auu____329 . (Prims.string * 'Auu____329)  ->  (Prims.string * 'Auu____329) = (fun uu____341 -> (match (uu____341) with
| (x, n1) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(

let uu____352 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((uu____352), (n1)))
end
| uu____353 -> begin
((x), (n1))
end)
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  FStar_Extraction_ML_Syntax.mlident = (fun id -> ((id.FStar_Ident.idText), ((Prims.parse_int "0"))))


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____370 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick uu____370)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____383 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick uu____383)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
mlt
end
| uu____434 -> begin
(lookup_ty_local tl1 b)
end)
end
| (Bv (b', FStar_Util.Inr (uu____436)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end
| uu____476 -> begin
(lookup_ty_local tl1 b)
end)
end
| (uu____477)::tl1 -> begin
(lookup_ty_local tl1 b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td : 'Auu____491 'Auu____492 'Auu____493 'Auu____494 . ('Auu____494 * 'Auu____493 * 'Auu____492 * FStar_Extraction_ML_Syntax.mlidents * 'Auu____491 * FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option)  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun uu____514 -> (match (uu____514) with
| (uu____529, uu____530, uu____531, vars, uu____533, body_opt) -> begin
(match (body_opt) with
| FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
FStar_Pervasives_Native.Some (((vars), (t)))
end
| uu____548 -> begin
FStar_Pervasives_Native.None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun env uu____560 -> (match (uu____560) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun uu____580 -> (match (uu____580) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(FStar_Util.find_map tds (fun td -> (

let uu____608 = td
in (match (uu____608) with
| (uu____611, n1, uu____613, uu____614, uu____615, uu____616) -> begin
(match ((n1 = ty_name)) with
| true -> begin
(tyscheme_of_td td)
end
| uu____629 -> begin
FStar_Pervasives_Native.None
end)
end))))
end
| uu____630 -> begin
FStar_Pervasives_Native.None
end)
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun uu____674 -> (match (uu____674) with
| (m, tds) -> begin
(FStar_Util.find_map tds (fun uu____708 -> (match (uu____708) with
| (uu____717, n1, mangle_opt, uu____720, uu____721, uu____722) -> begin
(match ((m = mname)) with
| true -> begin
(match ((n1 = ty_name)) with
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
| uu____777 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____784 -> begin
FStar_Pervasives_Native.None
end)
end)))
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___104_813 -> (match (uu___104_813) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____818 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____819 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (failwith uu____819))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___105_835 -> (match (uu___105_835) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____840 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____841 = (

let uu____842 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (

let uu____843 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" uu____842 uu____843)))
in (failwith uu____841))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___106_859 -> (match (uu___106_859) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____864 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____865 = (

let uu____866 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____867 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____866 uu____867)))
in (failwith uu____865))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let uu____898 = (lookup_bv g x1)
in ((uu____898), (FStar_Pervasives_Native.None)))
end
| FStar_Util.Inr (x1) -> begin
(

let uu____902 = (lookup_fv g x1)
in ((uu____902), (x1.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____927 -> begin
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

let uu___108_1001 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___108_1001.tydefs; type_names = uu___108_1001.type_names; currentModule = uu___108_1001.currentModule}))))))


let sanitize : Prims.string  ->  Prims.string = (fun s -> (

let cs = (FStar_String.list_of_string s)
in (

let valid = (fun c -> (((FStar_Util.is_letter_or_digit c) || (c = '_')) || (c = '\'')))
in (

let cs' = (FStar_List.fold_right (fun c cs1 -> (

let uu____1025 = (

let uu____1028 = (valid c)
in (match (uu____1028) with
| true -> begin
(c)::[]
end
| uu____1031 -> begin
('_')::('_')::[]
end))
in (FStar_List.append uu____1025 cs1))) cs [])
in (

let cs'1 = (match (cs') with
| (c)::cs1 when ((FStar_Util.is_digit c) || (c = '\'')) -> begin
('_')::(c)::cs1
end
| uu____1041 -> begin
cs
end)
in (FStar_String.string_of_list cs'1))))))


let find_uniq : binding Prims.list  ->  Prims.string  ->  Prims.string = (fun gamma mlident -> (

let rec find_uniq = (fun mlident1 i -> (

let suffix = (match ((i = (Prims.parse_int "0"))) with
| true -> begin
""
end
| uu____1064 -> begin
(FStar_Util.string_of_int i)
end)
in (

let target_mlident = (Prims.strcat mlident1 suffix)
in (

let has_collision = (FStar_List.existsb (fun uu___107_1071 -> (match (uu___107_1071) with
| Bv (uu____1072, FStar_Util.Inl (mlident', uu____1074)) -> begin
(target_mlident = (FStar_Pervasives_Native.fst mlident'))
end
| Fv (uu____1103, FStar_Util.Inl (mlident', uu____1105)) -> begin
(target_mlident = (FStar_Pervasives_Native.fst mlident'))
end
| Fv (uu____1134, FStar_Util.Inr (mlident', uu____1136, uu____1137, uu____1138)) -> begin
(target_mlident = mlident')
end
| Bv (uu____1167, FStar_Util.Inr (mlident', uu____1169, uu____1170, uu____1171)) -> begin
(target_mlident = mlident')
end)) gamma)
in (match (has_collision) with
| true -> begin
(find_uniq mlident1 (i + (Prims.parse_int "1")))
end
| uu____1200 -> begin
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
| uu____1238 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____1239 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (match (uu____1239) with
| (mlident, nocluewhat) -> begin
(

let mlsymbol = (find_uniq g.gamma mlident)
in (

let mlident1 = ((mlsymbol), (nocluewhat))
in (

let mlx = FStar_Extraction_ML_Syntax.MLE_Var (mlident1)
in (

let mlx1 = (match (mk_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1254 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____1257 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlsymbol), (mlx1), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (

let uu____1290 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____1290))
in (((

let uu___109_1296 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___109_1296.tydefs; type_names = uu___109_1296.type_names; currentModule = uu___109_1296.currentModule})), (mlident1))))))))
end))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____1309 = (mltyFvars t1)
in (

let uu____1312 = (mltyFvars t2)
in (FStar_List.append uu____1309 uu____1312)))
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

let uu____1348 = (mltyFvars (FStar_Pervasives_Native.snd tys))
in (subsetMlidents uu____1348 (FStar_Pervasives_Native.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x y t_x add_unit is_rec -> (

let uu____1383 = (tySchemeIsClosed t_x)
in (match (uu____1383) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____1392 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____1393 = (

let uu____1404 = y
in (match (uu____1404) with
| (ns, i) -> begin
(

let mlsymbol = (FStar_Extraction_ML_Syntax.avoid_keyword i)
in ((((ns), (mlsymbol))), (mlsymbol)))
end))
in (match (uu____1393) with
| (mlpath, mlsymbol) -> begin
(

let mly = FStar_Extraction_ML_Syntax.MLE_Name (mlpath)
in (

let mly1 = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____1452 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mlsymbol), (mly1), (t_x), (is_rec)))))))::g.gamma
in (((

let uu___110_1489 = g
in {tcenv = uu___110_1489.tcenv; gamma = gamma; tydefs = uu___110_1489.tydefs; type_names = uu___110_1489.type_names; currentModule = uu___110_1489.currentModule})), (((mlsymbol), ((Prims.parse_int "0"))))))))
end)))
end
| uu____1490 -> begin
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

let uu____1558 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1558) with
| (p, y) -> begin
(extend_fv' g f ((p), (y)) t_x add_unit is_rec)
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu___111_1586 = g
in {tcenv = uu___111_1586.tcenv; gamma = uu___111_1586.gamma; tydefs = (((m), (td)))::g.tydefs; type_names = (fv)::g.type_names; currentModule = uu___111_1586.currentModule})))


let extend_type_name : env  ->  FStar_Syntax_Syntax.fv  ->  env = (fun g fv -> (

let uu___112_1603 = g
in {tcenv = uu___112_1603.tcenv; gamma = uu___112_1603.gamma; tydefs = uu___112_1603.tydefs; type_names = (fv)::g.type_names; currentModule = uu___112_1603.currentModule}))


let is_type_name : env  ->  FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun g fv -> (FStar_All.pipe_right g.type_names (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))))


let emptyMlPath : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; type_names = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____1673 = (

let uu____1678 = (

let uu____1679 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____1679))
in (extend_lb env uu____1678 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right uu____1673 FStar_Pervasives_Native.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let lid = (FStar_Syntax_Util.mk_field_projector_name_from_ident ed.FStar_Syntax_Syntax.mname (FStar_Ident.id_of_text nm))
in (

let uu____1697 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1697), (lid)))))


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed a -> (

let nm = a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let module_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns
in (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append module_name (((FStar_Ident.id_of_text nm))::[])))
in (

let uu____1715 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1715), (lid)))))))




