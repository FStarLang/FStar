
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
| uu____28 -> begin
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
| uu____50 -> begin
false
end))


let __proj__Fv__item___0 : binding  ->  (FStar_Syntax_Syntax.fv * ty_or_exp_b) = (fun projectee -> (match (projectee) with
| Fv (_0) -> begin
_0
end))

type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let __proj__Mkenv__item__tcenv : env  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; currentModule = __fname__currentModule} -> begin
__fname__tcenv
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; currentModule = __fname__currentModule} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__tydefs : env  ->  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; currentModule = __fname__currentModule} -> begin
__fname__tydefs
end))


let __proj__Mkenv__item__currentModule : env  ->  FStar_Extraction_ML_Syntax.mlpath = (fun projectee -> (match (projectee) with
| {tcenv = __fname__tcenv; gamma = __fname__gamma; tydefs = __fname__tydefs; currentModule = __fname__currentModule} -> begin
__fname__currentModule
end))


let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> (

let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in (

let uu____162 = (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction")))
in (match (uu____162) with
| true -> begin
(f ())
end
| uu____163 -> begin
()
end))))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match ((t = FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| uu____176 -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____177, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| uu____184 -> begin
false
end)
end))


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick = (fun uu____197 -> (match (uu____197) with
| (x, n1) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
((x), (n1))
end
| uu____204 -> begin
(((Prims.strcat "\'A" x)), (n1))
end)
end))


let removeTick = (fun uu____217 -> (match (uu____217) with
| (x, n1) -> begin
(match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(

let uu____224 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((uu____224), (n1)))
end
| uu____225 -> begin
((x), (n1))
end)
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  FStar_Extraction_ML_Syntax.mlident = (fun id -> ((id.FStar_Ident.idText), ((Prims.parse_int "0"))))


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____240 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick uu____240)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (

let uu____249 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick uu____249)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
mlt
end
| uu____281 -> begin
(lookup_ty_local tl1 b)
end)
end
| (Bv (b', FStar_Util.Inr (uu____283)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end
| uu____304 -> begin
(lookup_ty_local tl1 b)
end)
end
| (uu____305)::tl1 -> begin
(lookup_ty_local tl1 b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td = (fun uu____329 -> (match (uu____329) with
| (uu____336, uu____337, uu____338, vars, body_opt) -> begin
(match (body_opt) with
| FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
FStar_Pervasives_Native.Some (((vars), (t)))
end
| uu____348 -> begin
FStar_Pervasives_Native.None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun env uu____358 -> (match (uu____358) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun uu____371 -> (match (uu____371) with
| (m, tds) -> begin
(match ((module_name = m)) with
| true -> begin
(FStar_Util.find_map tds (fun td -> (

let uu____390 = td
in (match (uu____390) with
| (uu____392, n1, uu____394, uu____395, uu____396) -> begin
(match ((n1 = ty_name)) with
| true -> begin
(tyscheme_of_td td)
end
| uu____403 -> begin
FStar_Pervasives_Native.None
end)
end))))
end
| uu____404 -> begin
FStar_Pervasives_Native.None
end)
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun uu____436 -> (match (uu____436) with
| (m, tds) -> begin
(FStar_Util.find_map tds (fun uu____457 -> (match (uu____457) with
| (uu____462, n1, mangle_opt, uu____465, uu____466) -> begin
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
| uu____495 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____499 -> begin
FStar_Pervasives_Native.None
end)
end)))
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___104_524 -> (match (uu___104_524) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____528 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____529 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (failwith uu____529))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___105_544 -> (match (uu___105_544) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____548 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____549 = (

let uu____550 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (

let uu____551 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" uu____550 uu____551)))
in (failwith uu____549))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___106_566 -> (match (uu___106_566) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____570 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____571 = (

let uu____572 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____573 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____572 uu____573)))
in (failwith uu____571))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let uu____594 = (lookup_bv g x1)
in ((uu____594), (FStar_Pervasives_Native.None)))
end
| FStar_Util.Inr (x1) -> begin
(

let uu____597 = (lookup_fv g x1)
in ((uu____597), (x1.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____615 -> begin
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

let uu___108_661 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___108_661.tydefs; currentModule = uu___108_661.currentModule}))))))


let sanitize : Prims.string  ->  Prims.string = (fun s -> (

let cs = (FStar_String.list_of_string s)
in (

let valid = (fun c -> (((FStar_Util.is_letter_or_digit c) || (c = '_')) || (c = '\'')))
in (

let cs' = (FStar_List.fold_right (fun c cs1 -> (

let uu____681 = (

let uu____683 = (valid c)
in (match (uu____683) with
| true -> begin
(c)::[]
end
| uu____685 -> begin
('_')::('_')::[]
end))
in (FStar_List.append uu____681 cs1))) cs [])
in (

let cs'1 = (match (cs') with
| (c)::cs1 when ((FStar_Util.is_digit c) || (c = '\'')) -> begin
('_')::(c)::cs1
end
| uu____692 -> begin
cs
end)
in (FStar_String.string_of_list cs'1))))))


let find_uniq : binding Prims.list  ->  Prims.string  ->  Prims.string = (fun gamma mlident -> (

let rec find_uniq = (fun mlident1 i -> (

let suffix = (match ((i = (Prims.parse_int "0"))) with
| true -> begin
""
end
| uu____712 -> begin
(FStar_Util.string_of_int i)
end)
in (

let target_mlident = (Prims.strcat mlident1 suffix)
in (

let has_collision = (FStar_List.existsb (fun uu___107_719 -> (match (uu___107_719) with
| Bv (uu____720, FStar_Util.Inl (mlident', uu____722)) -> begin
(target_mlident = (FStar_Pervasives_Native.fst mlident'))
end
| Fv (uu____737, FStar_Util.Inl (mlident', uu____739)) -> begin
(target_mlident = (FStar_Pervasives_Native.fst mlident'))
end
| Fv (uu____754, FStar_Util.Inr (mlident', uu____756, uu____757, uu____758)) -> begin
(target_mlident = mlident')
end
| Bv (uu____773, FStar_Util.Inr (mlident', uu____775, uu____776, uu____777)) -> begin
(target_mlident = mlident')
end)) gamma)
in (match (has_collision) with
| true -> begin
(find_uniq mlident1 (i + (Prims.parse_int "1")))
end
| uu____792 -> begin
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
| uu____825 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____826 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (match (uu____826) with
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
| uu____837 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____839 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlsymbol), (mlx1), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (

let uu____857 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____857))
in (((

let uu___109_861 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___109_861.tydefs; currentModule = uu___109_861.currentModule})), (mlident1))))))))
end))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____872 = (mltyFvars t1)
in (

let uu____874 = (mltyFvars t2)
in (FStar_List.append uu____872 uu____874)))
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

let uu____901 = (mltyFvars (FStar_Pervasives_Native.snd tys))
in (subsetMlidents uu____901 (FStar_Pervasives_Native.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g x y t_x add_unit is_rec -> (

let uu____931 = (tySchemeIsClosed t_x)
in (match (uu____931) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____937 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____938 = (

let uu____944 = y
in (match (uu____944) with
| (ns, i) -> begin
(

let mlsymbol = (FStar_Extraction_ML_Syntax.avoid_keyword i)
in ((((ns), (mlsymbol))), (mlsymbol)))
end))
in (match (uu____938) with
| (mlpath, mlsymbol) -> begin
(

let mly = FStar_Extraction_ML_Syntax.MLE_Name (mlpath)
in (

let mly1 = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____972 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mlsymbol), (mly1), (t_x), (is_rec)))))))::g.gamma
in (((

let uu___110_992 = g
in {tcenv = uu___110_992.tcenv; gamma = gamma; tydefs = uu___110_992.tydefs; currentModule = uu___110_992.currentModule})), (((mlsymbol), ((Prims.parse_int "0"))))))))
end)))
end
| uu____993 -> begin
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

let uu____1051 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1051) with
| (p, y) -> begin
(extend_fv' g f ((p), (y)) t_x add_unit is_rec)
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu___111_1073 = g
in {tcenv = uu___111_1073.tcenv; gamma = uu___111_1073.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = uu___111_1073.currentModule})))


let emptyMlPath : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____1111 = (

let uu____1114 = (

let uu____1115 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____1115))
in (extend_lb env uu____1114 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right uu____1111 FStar_Pervasives_Native.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let lid = (FStar_Syntax_Util.mk_field_projector_name_from_ident ed.FStar_Syntax_Syntax.mname (FStar_Ident.id_of_text nm))
in (

let uu____1129 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1129), (lid)))))


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed a -> (

let nm = a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let module_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns
in (

let lid = (FStar_Ident.lid_of_ids (FStar_List.append module_name (((FStar_Ident.id_of_text nm))::[])))
in (

let uu____1144 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1144), (lid)))))))




