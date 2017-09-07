
open Prims
open FStar_Pervasives

type name =
Prims.string Prims.list


type typ =
FStar_Syntax_Syntax.term


type binders =
FStar_Syntax_Syntax.binder Prims.list

type vconst =
| C_Unit
| C_Int of Prims.int
| C_True
| C_False
| C_String of Prims.string


let uu___is_C_Unit : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Unit -> begin
true
end
| uu____17 -> begin
false
end))


let uu___is_C_Int : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Int (_0) -> begin
true
end
| uu____23 -> begin
false
end))


let __proj__C_Int__item___0 : vconst  ->  Prims.int = (fun projectee -> (match (projectee) with
| C_Int (_0) -> begin
_0
end))


let uu___is_C_True : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_True -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_C_False : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_False -> begin
true
end
| uu____41 -> begin
false
end))


let uu___is_C_String : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_String (_0) -> begin
true
end
| uu____47 -> begin
false
end))


let __proj__C_String__item___0 : vconst  ->  Prims.string = (fun projectee -> (match (projectee) with
| C_String (_0) -> begin
_0
end))

type pattern =
| Pat_Constant of vconst
| Pat_Cons of (FStar_Syntax_Syntax.fv * pattern Prims.list)
| Pat_Var of FStar_Syntax_Syntax.bv
| Pat_Wild of FStar_Syntax_Syntax.bv


let uu___is_Pat_Constant : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Constant (_0) -> begin
true
end
| uu____83 -> begin
false
end))


let __proj__Pat_Constant__item___0 : pattern  ->  vconst = (fun projectee -> (match (projectee) with
| Pat_Constant (_0) -> begin
_0
end))


let uu___is_Pat_Cons : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Cons (_0) -> begin
true
end
| uu____103 -> begin
false
end))


let __proj__Pat_Cons__item___0 : pattern  ->  (FStar_Syntax_Syntax.fv * pattern Prims.list) = (fun projectee -> (match (projectee) with
| Pat_Cons (_0) -> begin
_0
end))


let uu___is_Pat_Var : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Var (_0) -> begin
true
end
| uu____135 -> begin
false
end))


let __proj__Pat_Var__item___0 : pattern  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Pat_Var (_0) -> begin
_0
end))


let uu___is_Pat_Wild : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Wild (_0) -> begin
true
end
| uu____149 -> begin
false
end))


let __proj__Pat_Wild__item___0 : pattern  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Pat_Wild (_0) -> begin
_0
end))


type branch =
(pattern * FStar_Syntax_Syntax.term)

type aqualv =
| Q_Implicit
| Q_Explicit


let uu___is_Q_Implicit : aqualv  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Q_Implicit -> begin
true
end
| uu____166 -> begin
false
end))


let uu___is_Q_Explicit : aqualv  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Q_Explicit -> begin
true
end
| uu____171 -> begin
false
end))


type argv =
(FStar_Syntax_Syntax.term * aqualv)

type term_view =
| Tv_Var of FStar_Syntax_Syntax.binder
| Tv_FVar of FStar_Syntax_Syntax.fv
| Tv_App of (FStar_Syntax_Syntax.term * argv)
| Tv_Abs of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Arrow of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Type of Prims.unit
| Tv_Refine of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Const of vconst
| Tv_Uvar of (Prims.int * typ)
| Tv_Match of (FStar_Syntax_Syntax.term * branch Prims.list)
| Tv_Unknown


let uu___is_Tv_Var : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Var (_0) -> begin
true
end
| uu____247 -> begin
false
end))


let __proj__Tv_Var__item___0 : term_view  ->  FStar_Syntax_Syntax.binder = (fun projectee -> (match (projectee) with
| Tv_Var (_0) -> begin
_0
end))


let uu___is_Tv_FVar : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_FVar (_0) -> begin
true
end
| uu____261 -> begin
false
end))


let __proj__Tv_FVar__item___0 : term_view  ->  FStar_Syntax_Syntax.fv = (fun projectee -> (match (projectee) with
| Tv_FVar (_0) -> begin
_0
end))


let uu___is_Tv_App : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_App (_0) -> begin
true
end
| uu____279 -> begin
false
end))


let __proj__Tv_App__item___0 : term_view  ->  (FStar_Syntax_Syntax.term * argv) = (fun projectee -> (match (projectee) with
| Tv_App (_0) -> begin
_0
end))


let uu___is_Tv_Abs : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Abs (_0) -> begin
true
end
| uu____309 -> begin
false
end))


let __proj__Tv_Abs__item___0 : term_view  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Tv_Abs (_0) -> begin
_0
end))


let uu___is_Tv_Arrow : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Arrow (_0) -> begin
true
end
| uu____339 -> begin
false
end))


let __proj__Tv_Arrow__item___0 : term_view  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Tv_Arrow (_0) -> begin
_0
end))


let uu___is_Tv_Type : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Type (_0) -> begin
true
end
| uu____365 -> begin
false
end))


let __proj__Tv_Type__item___0 : term_view  ->  Prims.unit = (fun projectee -> ())


let uu___is_Tv_Refine : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Refine (_0) -> begin
true
end
| uu____383 -> begin
false
end))


let __proj__Tv_Refine__item___0 : term_view  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Tv_Refine (_0) -> begin
_0
end))


let uu___is_Tv_Const : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Const (_0) -> begin
true
end
| uu____409 -> begin
false
end))


let __proj__Tv_Const__item___0 : term_view  ->  vconst = (fun projectee -> (match (projectee) with
| Tv_Const (_0) -> begin
_0
end))


let uu___is_Tv_Uvar : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Uvar (_0) -> begin
true
end
| uu____427 -> begin
false
end))


let __proj__Tv_Uvar__item___0 : term_view  ->  (Prims.int * typ) = (fun projectee -> (match (projectee) with
| Tv_Uvar (_0) -> begin
_0
end))


let uu___is_Tv_Match : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Match (_0) -> begin
true
end
| uu____459 -> begin
false
end))


let __proj__Tv_Match__item___0 : term_view  ->  (FStar_Syntax_Syntax.term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Tv_Match (_0) -> begin
_0
end))


let uu___is_Tv_Unknown : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Unknown -> begin
true
end
| uu____490 -> begin
false
end))

type ctor =
| Ctor of (name * typ)


let uu___is_Ctor : ctor  ->  Prims.bool = (fun projectee -> true)


let __proj__Ctor__item___0 : ctor  ->  (name * typ) = (fun projectee -> (match (projectee) with
| Ctor (_0) -> begin
_0
end))

type sigelt_view =
| Sg_Inductive of (name * FStar_Syntax_Syntax.binder Prims.list * typ * ctor Prims.list)
| Unk


let uu___is_Sg_Inductive : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sg_Inductive (_0) -> begin
true
end
| uu____553 -> begin
false
end))


let __proj__Sg_Inductive__item___0 : sigelt_view  ->  (name * FStar_Syntax_Syntax.binder Prims.list * typ * ctor Prims.list) = (fun projectee -> (match (projectee) with
| Sg_Inductive (_0) -> begin
_0
end))


let uu___is_Unk : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unk -> begin
true
end
| uu____602 -> begin
false
end))

type norm_step =
| Simpl
| WHNF
| Primops
| Delta
| UnfoldOnly of FStar_Syntax_Syntax.fv Prims.list


let uu___is_Simpl : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simpl -> begin
true
end
| uu____613 -> begin
false
end))


let uu___is_WHNF : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WHNF -> begin
true
end
| uu____618 -> begin
false
end))


let uu___is_Primops : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____623 -> begin
false
end))


let uu___is_Delta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta -> begin
true
end
| uu____628 -> begin
false
end))


let uu___is_UnfoldOnly : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____636 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : norm_step  ->  FStar_Syntax_Syntax.fv Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let fstar_refl_lid : Prims.string Prims.list  ->  FStar_Ident.lident = (fun s -> (FStar_Ident.lid_of_path (FStar_List.append (("FStar")::("Reflection")::[]) s) FStar_Range.dummyRange))


let fstar_refl_basic_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Basic")::(s)::[])))


let fstar_refl_types_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Types")::(s)::[])))


let fstar_refl_syntax_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Syntax")::(s)::[])))


let fstar_refl_data_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Data")::(s)::[])))


let mk_refl_types_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____679 = (fstar_refl_types_lid s)
in (FStar_Syntax_Syntax.tconst uu____679)))


let mk_refl_syntax_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____684 = (fstar_refl_syntax_lid s)
in (FStar_Syntax_Syntax.tconst uu____684)))


let mk_refl_data_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____689 = (fstar_refl_data_lid s)
in (FStar_Syntax_Syntax.tconst uu____689)))


let fstar_refl_tdataconstr : Prims.string Prims.list  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____698 = (fstar_refl_lid s)
in (FStar_Syntax_Syntax.tdataconstr uu____698)))


let fstar_refl_term : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "term")


let fstar_refl_aqualv : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "aqualv")


let fstar_refl_env : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "env")


let fstar_refl_fvar : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "fv")


let fstar_refl_binder : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "binder")


let fstar_refl_binders : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "binders")


let fstar_refl_term_view : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "term_view")


let fstar_refl_sigelt : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "sigelt")


let fstar_refl_ctor : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "ctor")


let fstar_refl_pattern : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "pattern")


let fstar_refl_branch : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "branch")


let ref_Q_Explicit_lid : FStar_Ident.lident = (fstar_refl_data_lid "Q_Explicit")


let ref_Q_Implicit_lid : FStar_Ident.lident = (fstar_refl_data_lid "Q_Implicit")


let ref_Q_Explicit : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Q_Explicit_lid)


let ref_Q_Implicit : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Q_Implicit_lid)


let ref_C_Unit_lid : FStar_Ident.lident = (fstar_refl_data_lid "C_Unit")


let ref_C_True_lid : FStar_Ident.lident = (fstar_refl_data_lid "C_True")


let ref_C_False_lid : FStar_Ident.lident = (fstar_refl_data_lid "C_False")


let ref_C_Int_lid : FStar_Ident.lident = (fstar_refl_data_lid "C_Int")


let ref_C_String_lid : FStar_Ident.lident = (fstar_refl_data_lid "C_String")


let ref_C_Unit : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_Unit_lid)


let ref_C_True : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_True_lid)


let ref_C_False : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_False_lid)


let ref_C_Int : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_Int_lid)


let ref_C_String : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_String_lid)


let ref_Pat_Constant_lid : FStar_Ident.lident = (fstar_refl_data_lid "Pat_Constant")


let ref_Pat_Cons_lid : FStar_Ident.lident = (fstar_refl_data_lid "Pat_Cons")


let ref_Pat_Var_lid : FStar_Ident.lident = (fstar_refl_data_lid "Pat_Var")


let ref_Pat_Wild_lid : FStar_Ident.lident = (fstar_refl_data_lid "Pat_Wild")


let ref_Pat_Constant : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Constant_lid)


let ref_Pat_Cons : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Cons_lid)


let ref_Pat_Var : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Var_lid)


let ref_Pat_Wild : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Wild_lid)


let ref_Tv_Var_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Var")


let ref_Tv_FVar_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_FVar")


let ref_Tv_App_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_App")


let ref_Tv_Abs_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Abs")


let ref_Tv_Arrow_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Arrow")


let ref_Tv_Type_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Type")


let ref_Tv_Refine_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Refine")


let ref_Tv_Const_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Const")


let ref_Tv_Uvar_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Uvar")


let ref_Tv_Match_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Match")


let ref_Tv_Unknown_lid : FStar_Ident.lident = (fstar_refl_data_lid "Tv_Unknown")


let ref_Tv_Var : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Var_lid)


let ref_Tv_FVar : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_FVar_lid)


let ref_Tv_App : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_App_lid)


let ref_Tv_Abs : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Abs_lid)


let ref_Tv_Arrow : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Arrow_lid)


let ref_Tv_Type : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Type_lid)


let ref_Tv_Refine : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Refine_lid)


let ref_Tv_Const : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Const_lid)


let ref_Tv_Uvar : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Uvar_lid)


let ref_Tv_Match : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Match_lid)


let ref_Tv_Unknown : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Tv_Unknown_lid)


let ref_Sg_Inductive_lid : FStar_Ident.lident = (fstar_refl_data_lid "Sg_Inductive")


let ref_Unk_lid : FStar_Ident.lident = (fstar_refl_data_lid "Unk")


let ref_Ctor_lid : FStar_Ident.lident = (fstar_refl_data_lid "Ctor")


let ref_Sg_Inductive : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Sg_Inductive_lid)


let ref_Unk : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Unk_lid)


let ref_Ctor : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Ctor_lid)


let fstar_refl_norm_step : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "norm_step")


let ref_Simpl_lid : FStar_Ident.lident = (fstar_refl_data_lid "Simpl")


let ref_WHNF_lid : FStar_Ident.lident = (fstar_refl_data_lid "WHNF")


let ref_Primops_lid : FStar_Ident.lident = (fstar_refl_data_lid "Primops")


let ref_Delta_lid : FStar_Ident.lident = (fstar_refl_data_lid "Delta")


let ref_UnfoldOnly_lid : FStar_Ident.lident = (fstar_refl_data_lid "UnfoldOnly")


let ref_Simpl : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Simpl_lid)


let ref_WHNF : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_WHNF_lid)


let ref_Primops : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Primops_lid)


let ref_Delta : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Delta_lid)


let ref_UnfoldOnly : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_UnfoldOnly_lid)


let t_binder : FStar_Syntax_Syntax.term = (

let uu____699 = (fstar_refl_types_lid "binder")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____699))


let t_term : FStar_Syntax_Syntax.term = (

let uu____700 = (fstar_refl_types_lid "term")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____700))


let t_fv : FStar_Syntax_Syntax.term = (

let uu____701 = (fstar_refl_types_lid "fv")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____701))


let t_binders : FStar_Syntax_Syntax.term = (

let uu____702 = (fstar_refl_types_lid "binders")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____702))


let t_norm_step : FStar_Syntax_Syntax.term = (

let uu____703 = (fstar_refl_types_lid "norm_step")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____703))


let ord_Lt_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Lt")::[]) FStar_Range.dummyRange)


let ord_Eq_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Eq")::[]) FStar_Range.dummyRange)


let ord_Gt_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Gt")::[]) FStar_Range.dummyRange)


let ord_Lt : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Lt_lid)


let ord_Eq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Eq_lid)


let ord_Gt : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Gt_lid)




