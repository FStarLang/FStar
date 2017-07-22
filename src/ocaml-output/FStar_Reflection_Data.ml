
open Prims
open FStar_Pervasives

type name =
Prims.string Prims.list

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
| uu____15 -> begin
false
end))


let uu___is_C_Int : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Int (_0) -> begin
true
end
| uu____21 -> begin
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
| uu____34 -> begin
false
end))


let uu___is_C_False : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_False -> begin
true
end
| uu____39 -> begin
false
end))


let uu___is_C_String : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_String (_0) -> begin
true
end
| uu____45 -> begin
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
| uu____81 -> begin
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
| uu____101 -> begin
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
| uu____133 -> begin
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
| uu____147 -> begin
false
end))


let __proj__Pat_Wild__item___0 : pattern  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Pat_Wild (_0) -> begin
_0
end))


type branch =
(pattern * FStar_Syntax_Syntax.term)

type term_view =
| Tv_Var of FStar_Syntax_Syntax.binder
| Tv_FVar of FStar_Syntax_Syntax.fv
| Tv_App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
| Tv_Abs of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Arrow of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Type of Prims.unit
| Tv_Refine of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Const of vconst
| Tv_Uvar of (Prims.int * FStar_Syntax_Syntax.typ)
| Tv_Match of (FStar_Syntax_Syntax.term * branch Prims.list)
| Tv_Unknown


let uu___is_Tv_Var : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Var (_0) -> begin
true
end
| uu____231 -> begin
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
| uu____245 -> begin
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
| uu____263 -> begin
false
end))


let __proj__Tv_App__item___0 : term_view  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Tv_App (_0) -> begin
_0
end))


let uu___is_Tv_Abs : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Abs (_0) -> begin
true
end
| uu____293 -> begin
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
| uu____323 -> begin
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
| uu____349 -> begin
false
end))


let __proj__Tv_Type__item___0 : term_view  ->  Prims.unit = (fun projectee -> ())


let uu___is_Tv_Refine : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Refine (_0) -> begin
true
end
| uu____367 -> begin
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
| uu____393 -> begin
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
| uu____411 -> begin
false
end))


let __proj__Tv_Uvar__item___0 : term_view  ->  (Prims.int * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| Tv_Uvar (_0) -> begin
_0
end))


let uu___is_Tv_Match : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Match (_0) -> begin
true
end
| uu____443 -> begin
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
| uu____474 -> begin
false
end))

type ctor =
| Ctor of (name * FStar_Syntax_Syntax.typ)


let uu___is_Ctor : ctor  ->  Prims.bool = (fun projectee -> true)


let __proj__Ctor__item___0 : ctor  ->  (name * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| Ctor (_0) -> begin
_0
end))

type sigelt_view =
| Sg_Inductive of (name * FStar_Syntax_Syntax.binder Prims.list * FStar_Syntax_Syntax.typ * ctor Prims.list)
| Unk


let uu___is_Sg_Inductive : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sg_Inductive (_0) -> begin
true
end
| uu____537 -> begin
false
end))


let __proj__Sg_Inductive__item___0 : sigelt_view  ->  (name * FStar_Syntax_Syntax.binder Prims.list * FStar_Syntax_Syntax.typ * ctor Prims.list) = (fun projectee -> (match (projectee) with
| Sg_Inductive (_0) -> begin
_0
end))


let uu___is_Unk : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unk -> begin
true
end
| uu____586 -> begin
false
end))

type norm_step =
| Simpl
| WHNF
| Primops
| Delta


let uu___is_Simpl : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simpl -> begin
true
end
| uu____591 -> begin
false
end))


let uu___is_WHNF : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WHNF -> begin
true
end
| uu____596 -> begin
false
end))


let uu___is_Primops : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____601 -> begin
false
end))


let uu___is_Delta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta -> begin
true
end
| uu____606 -> begin
false
end))


let fstar_refl_lid : Prims.string Prims.list  ->  FStar_Ident.lident = (fun s -> (FStar_Ident.lid_of_path (FStar_List.append (("FStar")::("Reflection")::[]) s) FStar_Range.dummyRange))


let fstar_refl_types_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Types")::(s)::[])))


let fstar_refl_syntax_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Syntax")::(s)::[])))


let mk_refl_types_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____627 = (fstar_refl_types_lid s)
in (FStar_Syntax_Syntax.tconst uu____627)))


let mk_refl_syntax_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____632 = (fstar_refl_syntax_lid s)
in (FStar_Syntax_Syntax.tconst uu____632)))


let fstar_refl_tdataconstr : Prims.string Prims.list  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____641 = (fstar_refl_lid s)
in (FStar_Syntax_Syntax.tdataconstr uu____641)))


let fstar_refl_term : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "term")


let fstar_refl_env : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "env")


let fstar_refl_fvar : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "fv")


let fstar_refl_binder : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "binder")


let fstar_refl_binders : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "binders")


let fstar_refl_term_view : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "term_view")


let fstar_refl_sigelt : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "sigelt")


let fstar_refl_ctor : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "ctor")


let fstar_refl_pattern : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "pattern")


let fstar_refl_branch : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "branch")


let ref_C_Unit_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "C_Unit")


let ref_C_True_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "C_True")


let ref_C_False_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "C_False")


let ref_C_Int_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "C_Int")


let ref_C_String_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "C_String")


let ref_C_Unit : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_Unit_lid)


let ref_C_True : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_True_lid)


let ref_C_False : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_False_lid)


let ref_C_Int : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_Int_lid)


let ref_C_String : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_C_String_lid)


let ref_Pat_Constant_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Pat_Constant")


let ref_Pat_Cons_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Pat_Cons")


let ref_Pat_Var_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Pat_Var")


let ref_Pat_Wild_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Pat_Wild")


let ref_Pat_Constant : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Constant_lid)


let ref_Pat_Cons : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Cons_lid)


let ref_Pat_Var : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Var_lid)


let ref_Pat_Wild : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Pat_Wild_lid)


let ref_Tv_Var_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Var")


let ref_Tv_FVar_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_FVar")


let ref_Tv_App_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_App")


let ref_Tv_Abs_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Abs")


let ref_Tv_Arrow_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Arrow")


let ref_Tv_Type_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Type")


let ref_Tv_Refine_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Refine")


let ref_Tv_Const_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Const")


let ref_Tv_Uvar_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Uvar")


let ref_Tv_Match_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Match")


let ref_Tv_Unknown_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Tv_Unknown")


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


let ref_Sg_Inductive_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Sg_Inductive")


let ref_Unk_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Unk")


let ref_Ctor_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Ctor")


let ref_Sg_Inductive : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Sg_Inductive_lid)


let ref_Unk : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Unk_lid)


let ref_Ctor : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Ctor_lid)

type order =
| Lt
| Eq
| Gt


let uu___is_Lt : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____646 -> begin
false
end))


let uu___is_Eq : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____651 -> begin
false
end))


let uu___is_Gt : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____656 -> begin
false
end))


let ord_Lt_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Lt")::[]) FStar_Range.dummyRange)


let ord_Eq_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Eq")::[]) FStar_Range.dummyRange)


let ord_Gt_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Gt")::[]) FStar_Range.dummyRange)


let ord_Lt : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Lt_lid)


let ord_Eq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Eq_lid)


let ord_Gt : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Gt_lid)


let fstar_refl_norm_step : FStar_Syntax_Syntax.term = (mk_refl_syntax_lid_as_term "norm_step")


let ref_Simpl_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Simpl")


let ref_WHNF_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "WHNF")


let ref_Primops_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Primops")


let ref_Delta_lid : FStar_Ident.lident = (fstar_refl_syntax_lid "Delta")


let ref_Simpl : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Simpl_lid)


let ref_WHNF : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_WHNF_lid)


let ref_Primops : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Primops_lid)


let ref_Delta : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ref_Delta_lid)


let t_binder : FStar_Syntax_Syntax.term = (

let uu____657 = (fstar_refl_types_lid "binder")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____657))


let t_term : FStar_Syntax_Syntax.term = (

let uu____658 = (fstar_refl_types_lid "term")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____658))


let t_fv : FStar_Syntax_Syntax.term = (

let uu____659 = (fstar_refl_types_lid "fv")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____659))


let t_binders : FStar_Syntax_Syntax.term = (

let uu____660 = (fstar_refl_syntax_lid "binders")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____660))


let t_norm_step : FStar_Syntax_Syntax.term = (

let uu____661 = (fstar_refl_syntax_lid "norm_step")
in (FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____661))




