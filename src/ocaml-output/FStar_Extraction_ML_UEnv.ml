
open Prims
open FStar_Pervasives
type ty_binding =
{ty_b_name : FStar_Extraction_ML_Syntax.mlident; ty_b_ty : FStar_Extraction_ML_Syntax.mlty}


let __proj__Mkty_binding__item__ty_b_name : ty_binding  ->  FStar_Extraction_ML_Syntax.mlident = (fun projectee -> (match (projectee) with
| {ty_b_name = ty_b_name; ty_b_ty = ty_b_ty} -> begin
ty_b_name
end))


let __proj__Mkty_binding__item__ty_b_ty : ty_binding  ->  FStar_Extraction_ML_Syntax.mlty = (fun projectee -> (match (projectee) with
| {ty_b_name = ty_b_name; ty_b_ty = ty_b_ty} -> begin
ty_b_ty
end))

type exp_binding =
{exp_b_name : FStar_Extraction_ML_Syntax.mlident; exp_b_expr : FStar_Extraction_ML_Syntax.mlexpr; exp_b_tscheme : FStar_Extraction_ML_Syntax.mltyscheme; exp_b_inst_ok : Prims.bool}


let __proj__Mkexp_binding__item__exp_b_name : exp_binding  ->  FStar_Extraction_ML_Syntax.mlident = (fun projectee -> (match (projectee) with
| {exp_b_name = exp_b_name; exp_b_expr = exp_b_expr; exp_b_tscheme = exp_b_tscheme; exp_b_inst_ok = exp_b_inst_ok} -> begin
exp_b_name
end))


let __proj__Mkexp_binding__item__exp_b_expr : exp_binding  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun projectee -> (match (projectee) with
| {exp_b_name = exp_b_name; exp_b_expr = exp_b_expr; exp_b_tscheme = exp_b_tscheme; exp_b_inst_ok = exp_b_inst_ok} -> begin
exp_b_expr
end))


let __proj__Mkexp_binding__item__exp_b_tscheme : exp_binding  ->  FStar_Extraction_ML_Syntax.mltyscheme = (fun projectee -> (match (projectee) with
| {exp_b_name = exp_b_name; exp_b_expr = exp_b_expr; exp_b_tscheme = exp_b_tscheme; exp_b_inst_ok = exp_b_inst_ok} -> begin
exp_b_tscheme
end))


let __proj__Mkexp_binding__item__exp_b_inst_ok : exp_binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {exp_b_name = exp_b_name; exp_b_expr = exp_b_expr; exp_b_tscheme = exp_b_tscheme; exp_b_inst_ok = exp_b_inst_ok} -> begin
exp_b_inst_ok
end))


type ty_or_exp_b =
(ty_binding, exp_binding) FStar_Util.either

type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * exp_binding)


let uu___is_Bv : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bv (_0) -> begin
true
end
| uu____113 -> begin
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
| uu____143 -> begin
false
end))


let __proj__Fv__item___0 : binding  ->  (FStar_Syntax_Syntax.fv * exp_binding) = (fun projectee -> (match (projectee) with
| Fv (_0) -> begin
_0
end))

type tydef =
{tydef_fv : FStar_Syntax_Syntax.fv; tydef_mlmodule_name : FStar_Extraction_ML_Syntax.mlsymbol Prims.list; tydef_name : FStar_Extraction_ML_Syntax.mlsymbol; tydef_mangled_name : FStar_Extraction_ML_Syntax.mlsymbol FStar_Pervasives_Native.option; tydef_def : FStar_Extraction_ML_Syntax.mltyscheme}


let __proj__Mktydef__item__tydef_fv : tydef  ->  FStar_Syntax_Syntax.fv = (fun projectee -> (match (projectee) with
| {tydef_fv = tydef_fv; tydef_mlmodule_name = tydef_mlmodule_name; tydef_name = tydef_name; tydef_mangled_name = tydef_mangled_name; tydef_def = tydef_def} -> begin
tydef_fv
end))


let __proj__Mktydef__item__tydef_mlmodule_name : tydef  ->  FStar_Extraction_ML_Syntax.mlsymbol Prims.list = (fun projectee -> (match (projectee) with
| {tydef_fv = tydef_fv; tydef_mlmodule_name = tydef_mlmodule_name; tydef_name = tydef_name; tydef_mangled_name = tydef_mangled_name; tydef_def = tydef_def} -> begin
tydef_mlmodule_name
end))


let __proj__Mktydef__item__tydef_name : tydef  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun projectee -> (match (projectee) with
| {tydef_fv = tydef_fv; tydef_mlmodule_name = tydef_mlmodule_name; tydef_name = tydef_name; tydef_mangled_name = tydef_mangled_name; tydef_def = tydef_def} -> begin
tydef_name
end))


let __proj__Mktydef__item__tydef_mangled_name : tydef  ->  FStar_Extraction_ML_Syntax.mlsymbol FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {tydef_fv = tydef_fv; tydef_mlmodule_name = tydef_mlmodule_name; tydef_name = tydef_name; tydef_mangled_name = tydef_mangled_name; tydef_def = tydef_def} -> begin
tydef_mangled_name
end))


let __proj__Mktydef__item__tydef_def : tydef  ->  FStar_Extraction_ML_Syntax.mltyscheme = (fun projectee -> (match (projectee) with
| {tydef_fv = tydef_fv; tydef_mlmodule_name = tydef_mlmodule_name; tydef_name = tydef_name; tydef_mangled_name = tydef_mangled_name; tydef_def = tydef_def} -> begin
tydef_def
end))

type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : tydef Prims.list; type_names : FStar_Syntax_Syntax.fv Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let __proj__Mkenv__item__tcenv : env  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; gamma = gamma; tydefs = tydefs; type_names = type_names; currentModule = currentModule} -> begin
tcenv
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; gamma = gamma; tydefs = tydefs; type_names = type_names; currentModule = currentModule} -> begin
gamma
end))


let __proj__Mkenv__item__tydefs : env  ->  tydef Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; gamma = gamma; tydefs = tydefs; type_names = type_names; currentModule = currentModule} -> begin
tydefs
end))


let __proj__Mkenv__item__type_names : env  ->  FStar_Syntax_Syntax.fv Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; gamma = gamma; tydefs = tydefs; type_names = type_names; currentModule = currentModule} -> begin
type_names
end))


let __proj__Mkenv__item__currentModule : env  ->  FStar_Extraction_ML_Syntax.mlpath = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; gamma = gamma; tydefs = tydefs; type_names = type_names; currentModule = currentModule} -> begin
currentModule
end))


let debug : env  ->  (unit  ->  unit)  ->  unit = (fun g f -> (

let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in (

let uu____409 = (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction")))
in (match (uu____409) with
| true -> begin
(f ())
end
| uu____410 -> begin
()
end))))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Erased


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> (match ((Prims.op_Equality t FStar_Extraction_ML_Syntax.ml_unit_ty)) with
| true -> begin
true
end
| uu____426 -> begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____427, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____434, (("FStar")::("Tactics")::("Effect")::[], "tactic")) -> begin
(

let uu____441 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____441 (FStar_Pervasives_Native.Some (FStar_Options.Plugin))))
end
| uu____446 -> begin
false
end)
end))


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick : Prims.string  ->  Prims.string = (fun x -> (match ((FStar_Util.starts_with x "\'")) with
| true -> begin
x
end
| uu____452 -> begin
(Prims.strcat "\'A" x)
end))


let removeTick : Prims.string  ->  Prims.string = (fun x -> (match ((FStar_Util.starts_with x "\'")) with
| true -> begin
(FStar_Util.substring_from x (Prims.parse_int "1"))
end
| uu____458 -> begin
x
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  FStar_Extraction_ML_Syntax.mlident = (fun id1 -> id1.FStar_Ident.idText)


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let uu____474 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick uu____474)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let uu____480 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick uu____480)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (ty_b)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
ty_b.ty_b_ty
end
| uu____500 -> begin
(lookup_ty_local tl1 b)
end)
end
| (Bv (b', FStar_Util.Inr (uu____502)))::tl1 -> begin
(match ((FStar_Syntax_Syntax.bv_eq b b')) with
| true -> begin
(failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end
| uu____506 -> begin
(lookup_ty_local tl1 b)
end)
end
| (uu____507)::tl1 -> begin
(lookup_ty_local tl1 b)
end
| [] -> begin
(failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td : 'Auu____521 'Auu____522 'Auu____523 'Auu____524 . ('Auu____521 * 'Auu____522 * 'Auu____523 * FStar_Extraction_ML_Syntax.mlidents * 'Auu____524 * FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option)  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun uu____545 -> (match (uu____545) with
| (uu____560, uu____561, uu____562, vars, uu____564, body_opt) -> begin
(match (body_opt) with
| FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
FStar_Pervasives_Native.Some (((vars), (t)))
end
| uu____575 -> begin
FStar_Pervasives_Native.None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option = (fun env uu____589 -> (match (uu____589) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun tydef -> (match (((Prims.op_Equality module_name tydef.tydef_mlmodule_name) && (Prims.op_Equality ty_name tydef.tydef_name))) with
| true -> begin
FStar_Pervasives_Native.Some (tydef.tydef_def)
end
| uu____606 -> begin
FStar_Pervasives_Native.None
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun tydef -> (match (((Prims.op_Equality tydef.tydef_mlmodule_name mname) && (Prims.op_Equality tydef.tydef_name ty_name))) with
| true -> begin
(match (tydef.tydef_mangled_name) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((mname), (ty_name)))
end
| FStar_Pervasives_Native.Some (mangled) -> begin
FStar_Pervasives_Native.Some (((mname), (mangled)))
end)
end
| uu____681 -> begin
FStar_Pervasives_Native.None
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun uu___236_714 -> (match (uu___236_714) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____719 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____720 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (failwith uu____720))
end
| FStar_Pervasives_Native.Some (y) -> begin
FStar_Util.Inr (y)
end)))


let try_lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  exp_binding FStar_Pervasives_Native.option = (fun g fv -> (FStar_Util.find_map g.gamma (fun uu___237_739 -> (match (uu___237_739) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____744 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  exp_binding = (fun g fv -> (

let uu____755 = (try_lookup_fv g fv)
in (match (uu____755) with
| FStar_Pervasives_Native.None -> begin
(

let uu____758 = (

let uu____759 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (

let uu____760 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" uu____759 uu____760)))
in (failwith uu____758))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun uu___238_778 -> (match (uu___238_778) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____783 -> begin
FStar_Pervasives_Native.None
end)))
in (match (x) with
| FStar_Pervasives_Native.None -> begin
(

let uu____784 = (

let uu____785 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (

let uu____786 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____785 uu____786)))
in (failwith uu____784))
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let uu____819 = (lookup_bv g x1)
in ((uu____819), (FStar_Pervasives_Native.None)))
end
| FStar_Util.Inr (x1) -> begin
(

let uu____823 = (

let uu____824 = (lookup_fv g x1)
in FStar_Util.Inr (uu____824))
in ((uu____823), (x1.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| uu____851 -> begin
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

let gamma = (Bv (((a), (FStar_Util.Inl ({ty_b_name = ml_a; ty_b_ty = mapped_to1})))))::g.gamma
in (

let tcenv = (FStar_TypeChecker_Env.push_bv g.tcenv a)
in (

let uu___240_884 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___240_884.tydefs; type_names = uu___240_884.type_names; currentModule = uu___240_884.currentModule}))))))


let sanitize : Prims.string  ->  Prims.string = (fun s -> (

let cs = (FStar_String.list_of_string s)
in (

let valid = (fun c -> (((FStar_Util.is_letter_or_digit c) || (Prims.op_Equality c 95 (*_*))) || (Prims.op_Equality c 39 (*'*))))
in (

let cs' = (FStar_List.fold_right (fun c cs1 -> (

let uu____923 = (

let uu____927 = (valid c)
in (match (uu____927) with
| true -> begin
(c)::[]
end
| uu____933 -> begin
(95 (*_*))::(95 (*_*))::[]
end))
in (FStar_List.append uu____923 cs1))) cs [])
in (

let cs'1 = (match (cs') with
| (c)::cs1 when ((FStar_Util.is_digit c) || (Prims.op_Equality c 39 (*'*))) -> begin
(95 (*_*))::(c)::cs1
end
| uu____960 -> begin
cs
end)
in (FStar_String.string_of_list cs'1))))))


let find_uniq : binding Prims.list  ->  Prims.string  ->  Prims.string = (fun gamma mlident -> (

let rec find_uniq = (fun mlident1 i -> (

let suffix = (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
""
end
| uu____990 -> begin
(FStar_Util.string_of_int i)
end)
in (

let target_mlident = (Prims.strcat mlident1 suffix)
in (

let has_collision = (FStar_List.existsb (fun uu___239_996 -> (match (uu___239_996) with
| Bv (uu____997, FStar_Util.Inl (ty_b)) -> begin
(Prims.op_Equality target_mlident ty_b.ty_b_name)
end
| Fv (uu____999, exp_b) -> begin
(Prims.op_Equality target_mlident exp_b.exp_b_name)
end
| Bv (uu____1001, FStar_Util.Inr (exp_b)) -> begin
(Prims.op_Equality target_mlident exp_b.exp_b_name)
end)) gamma)
in (match (has_collision) with
| true -> begin
(find_uniq mlident1 (i + (Prims.parse_int "1")))
end
| uu____1003 -> begin
target_mlident
end)))))
in (

let mlident1 = (sanitize mlident)
in (find_uniq mlident1 (Prims.parse_int "0")))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident * exp_binding) = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____1049 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mlident = (

let uu____1051 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (find_uniq g.gamma uu____1051))
in (

let mlx = FStar_Extraction_ML_Syntax.MLE_Var (mlident)
in (

let mlx1 = (match (mk_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1054 -> begin
(match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____1057 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end)
end)
in (

let t_x1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.pop_unit t_x)
end
| uu____1059 -> begin
t_x
end)
in (

let exp_binding = {exp_b_name = mlident; exp_b_expr = mlx1; exp_b_tscheme = t_x1; exp_b_inst_ok = is_rec}
in (

let gamma = (Bv (((x), (FStar_Util.Inr (exp_binding)))))::g.gamma
in (

let tcenv = (

let uu____1065 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv uu____1065))
in (((

let uu___241_1067 = g
in {tcenv = tcenv; gamma = gamma; tydefs = uu___241_1067.tydefs; type_names = uu___241_1067.type_names; currentModule = uu___241_1067.currentModule})), (mlident), (exp_binding)))))))))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____1081 = (mltyFvars t1)
in (

let uu____1084 = (mltyFvars t2)
in (FStar_List.append uu____1081 uu____1084)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(FStar_List.collect mltyFvars args)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(FStar_List.collect mltyFvars ts)
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
[]
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
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

let uu____1123 = (mltyFvars (FStar_Pervasives_Native.snd tys))
in (subsetMlidents uu____1123 (FStar_Pervasives_Native.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident * exp_binding) = (fun g x y t_x add_unit is_rec -> (

let uu____1168 = (tySchemeIsClosed t_x)
in (match (uu____1168) with
| true -> begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| uu____1177 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let uu____1178 = (

let uu____1183 = y
in (match (uu____1183) with
| (ns, i) -> begin
(

let mlsymbol = (FStar_Extraction_ML_Syntax.avoid_keyword i)
in ((((ns), (mlsymbol))), (mlsymbol)))
end))
in (match (uu____1178) with
| (mlpath, mlsymbol) -> begin
(

let mly = FStar_Extraction_ML_Syntax.MLE_Name (mlpath)
in (

let mly1 = (match (add_unit) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end
| uu____1209 -> begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end)
in (

let t_x1 = (match (add_unit) with
| true -> begin
(FStar_Extraction_ML_Syntax.pop_unit t_x)
end
| uu____1211 -> begin
t_x
end)
in (

let exp_binding = {exp_b_name = mlsymbol; exp_b_expr = mly1; exp_b_tscheme = t_x1; exp_b_inst_ok = is_rec}
in (

let gamma = (Fv (((x), (exp_binding))))::g.gamma
in (((

let uu___242_1217 = g
in {tcenv = uu___242_1217.tcenv; gamma = gamma; tydefs = uu___242_1217.tydefs; type_names = uu___242_1217.type_names; currentModule = uu___242_1217.currentModule})), (mlsymbol), (exp_binding)))))))
end)))
end
| uu____1218 -> begin
(failwith "freevars found")
end)))


let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident * exp_binding) = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident * exp_binding) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(extend_bv g x t_x add_unit is_rec false)
end
| FStar_Util.Inr (f) -> begin
(

let uu____1307 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____1307) with
| (p, y) -> begin
(extend_fv' g f ((p), (y)) t_x add_unit is_rec)
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.one_mltydecl  ->  (env * tydef) = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let uu____1348 = td
in (match (uu____1348) with
| (_assumed, name, mangled, vars, metadata, body_opt) -> begin
(

let tydef = (

let uu____1368 = (

let uu____1369 = (tyscheme_of_td td)
in (FStar_Option.get uu____1369))
in {tydef_fv = fv; tydef_mlmodule_name = m; tydef_name = name; tydef_mangled_name = mangled; tydef_def = uu____1368})
in (((

let uu___243_1375 = g
in {tcenv = uu___243_1375.tcenv; gamma = uu___243_1375.gamma; tydefs = (tydef)::g.tydefs; type_names = (fv)::g.type_names; currentModule = uu___243_1375.currentModule})), (tydef)))
end))))


let extend_type_name : env  ->  FStar_Syntax_Syntax.fv  ->  env = (fun g fv -> (

let uu___244_1386 = g
in {tcenv = uu___244_1386.tcenv; gamma = uu___244_1386.gamma; tydefs = uu___244_1386.tydefs; type_names = (fv)::g.type_names; currentModule = uu___244_1386.currentModule}))


let is_type_name : env  ->  FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun g fv -> (FStar_All.pipe_right g.type_names (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))))


let is_fv_type : env  ->  FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun g fv -> ((is_type_name g fv) || (FStar_All.pipe_right g.tydefs (FStar_Util.for_some (fun tydef -> (FStar_Syntax_Syntax.fv_eq fv tydef.tydef_fv))))))


let emptyMlPath : FStar_Extraction_ML_Syntax.mlpath = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; type_names = []; currentModule = emptyMlPath}
in (

let a = "\'a"
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (

let uu____1431 = (

let uu____1438 = (

let uu____1439 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____1439))
in (extend_lb env uu____1438 FStar_Syntax_Syntax.tun failwith_ty false false))
in (match (uu____1431) with
| (g, uu____1441, uu____1442) -> begin
g
end))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed nm -> (

let lid = (

let uu____1458 = (FStar_Ident.id_of_text nm)
in (FStar_Syntax_Util.mk_field_projector_name_from_ident ed.FStar_Syntax_Syntax.mname uu____1458))
in (

let uu____1459 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1459), (lid)))))


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident) = (fun ed a -> (

let nm = a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let module_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns
in (

let lid = (

let uu____1479 = (

let uu____1482 = (

let uu____1485 = (FStar_Ident.id_of_text nm)
in (uu____1485)::[])
in (FStar_List.append module_name uu____1482))
in (FStar_Ident.lid_of_ids uu____1479))
in (

let uu____1486 = (FStar_Extraction_ML_Syntax.mlpath_of_lident lid)
in ((uu____1486), (lid)))))))




