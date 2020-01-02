
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
| C_Int of FStar_BigInt.t
| C_True
| C_False
| C_String of Prims.string
| C_Range of FStar_Range.range
| C_Reify
| C_Reflect of name


let uu___is_C_Unit : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Unit -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_C_Int : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Int (_0) -> begin
true
end
| uu____52 -> begin
false
end))


let __proj__C_Int__item___0 : vconst  ->  FStar_BigInt.t = (fun projectee -> (match (projectee) with
| C_Int (_0) -> begin
_0
end))


let uu___is_C_True : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_True -> begin
true
end
| uu____70 -> begin
false
end))


let uu___is_C_False : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_False -> begin
true
end
| uu____81 -> begin
false
end))


let uu___is_C_String : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_String (_0) -> begin
true
end
| uu____94 -> begin
false
end))


let __proj__C_String__item___0 : vconst  ->  Prims.string = (fun projectee -> (match (projectee) with
| C_String (_0) -> begin
_0
end))


let uu___is_C_Range : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Range (_0) -> begin
true
end
| uu____116 -> begin
false
end))


let __proj__C_Range__item___0 : vconst  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| C_Range (_0) -> begin
_0
end))


let uu___is_C_Reify : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Reify -> begin
true
end
| uu____134 -> begin
false
end))


let uu___is_C_Reflect : vconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Reflect (_0) -> begin
true
end
| uu____146 -> begin
false
end))


let __proj__C_Reflect__item___0 : vconst  ->  name = (fun projectee -> (match (projectee) with
| C_Reflect (_0) -> begin
_0
end))

type pattern =
| Pat_Constant of vconst
| Pat_Cons of (FStar_Syntax_Syntax.fv * (pattern * Prims.bool) Prims.list)
| Pat_Var of FStar_Syntax_Syntax.bv
| Pat_Wild of FStar_Syntax_Syntax.bv
| Pat_Dot_Term of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)


let uu___is_Pat_Constant : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Constant (_0) -> begin
true
end
| uu____205 -> begin
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
| uu____235 -> begin
false
end))


let __proj__Pat_Cons__item___0 : pattern  ->  (FStar_Syntax_Syntax.fv * (pattern * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_Cons (_0) -> begin
_0
end))


let uu___is_Pat_Var : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Var (_0) -> begin
true
end
| uu____287 -> begin
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
| uu____306 -> begin
false
end))


let __proj__Pat_Wild__item___0 : pattern  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Pat_Wild (_0) -> begin
_0
end))


let uu___is_Pat_Dot_Term : pattern  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_Dot_Term (_0) -> begin
true
end
| uu____329 -> begin
false
end))


let __proj__Pat_Dot_Term__item___0 : pattern  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Pat_Dot_Term (_0) -> begin
_0
end))


type branch =
(pattern * FStar_Syntax_Syntax.term)

type aqualv =
| Q_Implicit
| Q_Explicit
| Q_Meta of FStar_Syntax_Syntax.term


let uu___is_Q_Implicit : aqualv  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Q_Implicit -> begin
true
end
| uu____368 -> begin
false
end))


let uu___is_Q_Explicit : aqualv  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Q_Explicit -> begin
true
end
| uu____379 -> begin
false
end))


let uu___is_Q_Meta : aqualv  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Q_Meta (_0) -> begin
true
end
| uu____391 -> begin
false
end))


let __proj__Q_Meta__item___0 : aqualv  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| Q_Meta (_0) -> begin
_0
end))


type argv =
(FStar_Syntax_Syntax.term * aqualv)

type term_view =
| Tv_Var of FStar_Syntax_Syntax.bv
| Tv_BVar of FStar_Syntax_Syntax.bv
| Tv_FVar of FStar_Syntax_Syntax.fv
| Tv_App of (FStar_Syntax_Syntax.term * argv)
| Tv_Abs of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)
| Tv_Arrow of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
| Tv_Type of unit
| Tv_Refine of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
| Tv_Const of vconst
| Tv_Uvar of (FStar_BigInt.t * FStar_Syntax_Syntax.ctx_uvar_and_subst)
| Tv_Let of (Prims.bool * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
| Tv_Match of (FStar_Syntax_Syntax.term * branch Prims.list)
| Tv_AscribedT of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
| Tv_AscribedC of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
| Tv_Unknown


let uu___is_Tv_Var : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Var (_0) -> begin
true
end
| uu____539 -> begin
false
end))


let __proj__Tv_Var__item___0 : term_view  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Tv_Var (_0) -> begin
_0
end))


let uu___is_Tv_BVar : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_BVar (_0) -> begin
true
end
| uu____558 -> begin
false
end))


let __proj__Tv_BVar__item___0 : term_view  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Tv_BVar (_0) -> begin
_0
end))


let uu___is_Tv_FVar : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_FVar (_0) -> begin
true
end
| uu____577 -> begin
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
| uu____600 -> begin
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
| uu____635 -> begin
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
| uu____670 -> begin
false
end))


let __proj__Tv_Arrow__item___0 : term_view  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) = (fun projectee -> (match (projectee) with
| Tv_Arrow (_0) -> begin
_0
end))


let uu___is_Tv_Type : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Type (_0) -> begin
true
end
| uu____701 -> begin
false
end))





let uu___is_Tv_Refine : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Refine (_0) -> begin
true
end
| uu____718 -> begin
false
end))


let __proj__Tv_Refine__item___0 : term_view  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Tv_Refine (_0) -> begin
_0
end))


let uu___is_Tv_Const : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Const (_0) -> begin
true
end
| uu____749 -> begin
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
| uu____772 -> begin
false
end))


let __proj__Tv_Uvar__item___0 : term_view  ->  (FStar_BigInt.t * FStar_Syntax_Syntax.ctx_uvar_and_subst) = (fun projectee -> (match (projectee) with
| Tv_Uvar (_0) -> begin
_0
end))


let uu___is_Tv_Let : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Let (_0) -> begin
true
end
| uu____816 -> begin
false
end))


let __proj__Tv_Let__item___0 : term_view  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Tv_Let (_0) -> begin
_0
end))


let uu___is_Tv_Match : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Match (_0) -> begin
true
end
| uu____880 -> begin
false
end))


let __proj__Tv_Match__item___0 : term_view  ->  (FStar_Syntax_Syntax.term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Tv_Match (_0) -> begin
_0
end))


let uu___is_Tv_AscribedT : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_AscribedT (_0) -> begin
true
end
| uu____925 -> begin
false
end))


let __proj__Tv_AscribedT__item___0 : term_view  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tv_AscribedT (_0) -> begin
_0
end))


let uu___is_Tv_AscribedC : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_AscribedC (_0) -> begin
true
end
| uu____976 -> begin
false
end))


let __proj__Tv_AscribedC__item___0 : term_view  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tv_AscribedC (_0) -> begin
_0
end))


let uu___is_Tv_Unknown : term_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tv_Unknown -> begin
true
end
| uu____1018 -> begin
false
end))

type qualifier =
| Assumption
| New
| Private
| Unfold_for_unification_and_vcgen
| Visible_default
| Irreducible
| Abstract
| Inline_for_extraction
| NoExtract
| Noeq
| Unopteq
| TotalEffect
| Logic
| Reifiable
| Reflectable of FStar_Ident.lid
| Discriminator of FStar_Ident.lid
| Projector of (FStar_Ident.lid * FStar_Ident.ident)
| RecordType of (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list)
| RecordConstructor of (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list)
| Action of FStar_Ident.lid
| ExceptionConstructor
| HasMaskedEffect
| Effect
| OnlyName


let uu___is_Assumption : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumption -> begin
true
end
| uu____1079 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____1090 -> begin
false
end))


let uu___is_Private : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____1101 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____1112 -> begin
false
end))


let uu___is_Visible_default : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible_default -> begin
true
end
| uu____1123 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____1134 -> begin
false
end))


let uu___is_Abstract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____1145 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____1156 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____1167 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____1178 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____1189 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____1200 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____1211 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____1222 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable (_0) -> begin
true
end
| uu____1234 -> begin
false
end))


let __proj__Reflectable__item___0 : qualifier  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Reflectable (_0) -> begin
_0
end))


let uu___is_Discriminator : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Discriminator (_0) -> begin
true
end
| uu____1253 -> begin
false
end))


let __proj__Discriminator__item___0 : qualifier  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Discriminator (_0) -> begin
_0
end))


let uu___is_Projector : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Projector (_0) -> begin
true
end
| uu____1276 -> begin
false
end))


let __proj__Projector__item___0 : qualifier  ->  (FStar_Ident.lid * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_0) -> begin
_0
end))


let uu___is_RecordType : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RecordType (_0) -> begin
true
end
| uu____1315 -> begin
false
end))


let __proj__RecordType__item___0 : qualifier  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun projectee -> (match (projectee) with
| RecordType (_0) -> begin
_0
end))


let uu___is_RecordConstructor : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RecordConstructor (_0) -> begin
true
end
| uu____1366 -> begin
false
end))


let __proj__RecordConstructor__item___0 : qualifier  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun projectee -> (match (projectee) with
| RecordConstructor (_0) -> begin
_0
end))


let uu___is_Action : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Action (_0) -> begin
true
end
| uu____1409 -> begin
false
end))


let __proj__Action__item___0 : qualifier  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Action (_0) -> begin
_0
end))


let uu___is_ExceptionConstructor : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ExceptionConstructor -> begin
true
end
| uu____1427 -> begin
false
end))


let uu___is_HasMaskedEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HasMaskedEffect -> begin
true
end
| uu____1438 -> begin
false
end))


let uu___is_Effect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect -> begin
true
end
| uu____1449 -> begin
false
end))


let uu___is_OnlyName : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OnlyName -> begin
true
end
| uu____1460 -> begin
false
end))

type bv_view =
{bv_ppname : Prims.string; bv_index : FStar_BigInt.t; bv_sort : typ}


let __proj__Mkbv_view__item__bv_ppname : bv_view  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bv_ppname = bv_ppname; bv_index = bv_index; bv_sort = bv_sort} -> begin
bv_ppname
end))


let __proj__Mkbv_view__item__bv_index : bv_view  ->  FStar_BigInt.t = (fun projectee -> (match (projectee) with
| {bv_ppname = bv_ppname; bv_index = bv_index; bv_sort = bv_sort} -> begin
bv_index
end))


let __proj__Mkbv_view__item__bv_sort : bv_view  ->  typ = (fun projectee -> (match (projectee) with
| {bv_ppname = bv_ppname; bv_index = bv_index; bv_sort = bv_sort} -> begin
bv_sort
end))


type binder_view =
(FStar_Syntax_Syntax.bv * aqualv)

type comp_view =
| C_Total of (typ * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
| C_Lemma of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
| C_Unknown


let uu___is_C_Total : comp_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Total (_0) -> begin
true
end
| uu____1550 -> begin
false
end))


let __proj__C_Total__item___0 : comp_view  ->  (typ * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| C_Total (_0) -> begin
_0
end))


let uu___is_C_Lemma : comp_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Lemma (_0) -> begin
true
end
| uu____1591 -> begin
false
end))


let __proj__C_Lemma__item___0 : comp_view  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| C_Lemma (_0) -> begin
_0
end))


let uu___is_C_Unknown : comp_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| C_Unknown -> begin
true
end
| uu____1621 -> begin
false
end))

type sigelt_view =
| Sg_Let of (Prims.bool * FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.univ_name Prims.list * typ * FStar_Syntax_Syntax.term)
| Sg_Inductive of (name * FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.binder Prims.list * typ * name Prims.list)
| Sg_Constructor of (name * typ)
| Unk


let uu___is_Sg_Let : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sg_Let (_0) -> begin
true
end
| uu____1694 -> begin
false
end))


let __proj__Sg_Let__item___0 : sigelt_view  ->  (Prims.bool * FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.univ_name Prims.list * typ * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| Sg_Let (_0) -> begin
_0
end))


let uu___is_Sg_Inductive : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sg_Inductive (_0) -> begin
true
end
| uu____1768 -> begin
false
end))


let __proj__Sg_Inductive__item___0 : sigelt_view  ->  (name * FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.binder Prims.list * typ * name Prims.list) = (fun projectee -> (match (projectee) with
| Sg_Inductive (_0) -> begin
_0
end))


let uu___is_Sg_Constructor : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sg_Constructor (_0) -> begin
true
end
| uu____1839 -> begin
false
end))


let __proj__Sg_Constructor__item___0 : sigelt_view  ->  (name * typ) = (fun projectee -> (match (projectee) with
| Sg_Constructor (_0) -> begin
_0
end))


let uu___is_Unk : sigelt_view  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unk -> begin
true
end
| uu____1869 -> begin
false
end))


type var =
FStar_BigInt.t

type exp =
| Unit
| Var of var
| Mult of (exp * exp)


let uu___is_Unit : exp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unit -> begin
true
end
| uu____1894 -> begin
false
end))


let uu___is_Var : exp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____1906 -> begin
false
end))


let __proj__Var__item___0 : exp  ->  var = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
_0
end))


let uu___is_Mult : exp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mult (_0) -> begin
true
end
| uu____1929 -> begin
false
end))


let __proj__Mult__item___0 : exp  ->  (exp * exp) = (fun projectee -> (match (projectee) with
| Mult (_0) -> begin
_0
end))

type refl_constant =
{lid : FStar_Ident.lid; fv : FStar_Syntax_Syntax.fv; t : FStar_Syntax_Syntax.term}


let __proj__Mkrefl_constant__item__lid : refl_constant  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {lid = lid; fv = fv; t = t} -> begin
lid
end))


let __proj__Mkrefl_constant__item__fv : refl_constant  ->  FStar_Syntax_Syntax.fv = (fun projectee -> (match (projectee) with
| {lid = lid; fv = fv; t = t} -> begin
fv
end))


let __proj__Mkrefl_constant__item__t : refl_constant  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {lid = lid; fv = fv; t = t} -> begin
t
end))


let refl_constant_lid : refl_constant  ->  FStar_Ident.lid = (fun rc -> rc.lid)


let refl_constant_term : refl_constant  ->  FStar_Syntax_Syntax.term = (fun rc -> rc.t)


let fstar_refl_lid : Prims.string Prims.list  ->  FStar_Ident.lident = (fun s -> (FStar_Ident.lid_of_path (FStar_List.append (("FStar")::("Reflection")::[]) s) FStar_Range.dummyRange))


let fstar_refl_basic_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Basic")::(s)::[])))


let fstar_refl_syntax_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Syntax")::(s)::[])))


let fstar_refl_types_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Types")::(s)::[])))


let fstar_refl_data_lid : Prims.string  ->  FStar_Ident.lident = (fun s -> (fstar_refl_lid (("Data")::(s)::[])))


let fstar_refl_data_const : Prims.string  ->  refl_constant = (fun s -> (

let lid = (fstar_refl_data_lid s)
in (

let uu____2079 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (

let uu____2080 = (FStar_Syntax_Syntax.tdataconstr lid)
in {lid = lid; fv = uu____2079; t = uu____2080}))))


let mk_refl_types_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____2089 = (fstar_refl_types_lid s)
in (FStar_Syntax_Syntax.tconst uu____2089)))


let mk_refl_types_lid_as_fv : Prims.string  ->  FStar_Syntax_Syntax.fv = (fun s -> (

let uu____2098 = (fstar_refl_types_lid s)
in (FStar_Syntax_Syntax.fvconst uu____2098)))


let mk_refl_syntax_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____2107 = (fstar_refl_syntax_lid s)
in (FStar_Syntax_Syntax.tconst uu____2107)))


let mk_refl_syntax_lid_as_fv : Prims.string  ->  FStar_Syntax_Syntax.fv = (fun s -> (

let uu____2116 = (fstar_refl_syntax_lid s)
in (FStar_Syntax_Syntax.fvconst uu____2116)))


let mk_refl_data_lid_as_term : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____2125 = (fstar_refl_data_lid s)
in (FStar_Syntax_Syntax.tconst uu____2125)))


let mk_refl_data_lid_as_fv : Prims.string  ->  FStar_Syntax_Syntax.fv = (fun s -> (

let uu____2134 = (fstar_refl_data_lid s)
in (FStar_Syntax_Syntax.fvconst uu____2134)))


let mk_inspect_pack_pair : Prims.string  ->  (refl_constant * refl_constant) = (fun s -> (

let inspect_lid = (fstar_refl_basic_lid (Prims.op_Hat "inspect" s))
in (

let pack_lid = (fstar_refl_basic_lid (Prims.op_Hat "pack" s))
in (

let inspect_fv = (FStar_Syntax_Syntax.lid_as_fv inspect_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let pack_fv = (FStar_Syntax_Syntax.lid_as_fv pack_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let inspect1 = (

let uu____2156 = (FStar_Syntax_Syntax.fv_to_tm inspect_fv)
in {lid = inspect_lid; fv = inspect_fv; t = uu____2156})
in (

let pack1 = (

let uu____2158 = (FStar_Syntax_Syntax.fv_to_tm pack_fv)
in {lid = pack_lid; fv = pack_fv; t = uu____2158})
in ((inspect1), (pack1)))))))))


let uu___77 : (refl_constant * refl_constant) = (mk_inspect_pack_pair "_ln")


let fstar_refl_inspect_ln : refl_constant = (match (uu___77) with
| (fstar_refl_inspect_ln, fstar_refl_pack_ln) -> begin
fstar_refl_inspect_ln
end)


let fstar_refl_pack_ln : refl_constant = (match (uu___77) with
| (fstar_refl_inspect_ln1, fstar_refl_pack_ln) -> begin
fstar_refl_pack_ln
end)


let uu___84 : (refl_constant * refl_constant) = (mk_inspect_pack_pair "_fv")


let fstar_refl_inspect_fv : refl_constant = (match (uu___84) with
| (fstar_refl_inspect_fv, fstar_refl_pack_fv) -> begin
fstar_refl_inspect_fv
end)


let fstar_refl_pack_fv : refl_constant = (match (uu___84) with
| (fstar_refl_inspect_fv1, fstar_refl_pack_fv) -> begin
fstar_refl_pack_fv
end)


let uu___91 : (refl_constant * refl_constant) = (mk_inspect_pack_pair "_bv")


let fstar_refl_inspect_bv : refl_constant = (match (uu___91) with
| (fstar_refl_inspect_bv, fstar_refl_pack_bv) -> begin
fstar_refl_inspect_bv
end)


let fstar_refl_pack_bv : refl_constant = (match (uu___91) with
| (fstar_refl_inspect_bv1, fstar_refl_pack_bv) -> begin
fstar_refl_pack_bv
end)


let uu___98 : (refl_constant * refl_constant) = (mk_inspect_pack_pair "_binder")


let fstar_refl_inspect_binder : refl_constant = (match (uu___98) with
| (fstar_refl_inspect_binder, fstar_refl_pack_binder) -> begin
fstar_refl_inspect_binder
end)


let fstar_refl_pack_binder : refl_constant = (match (uu___98) with
| (fstar_refl_inspect_binder1, fstar_refl_pack_binder) -> begin
fstar_refl_pack_binder
end)


let uu___105 : (refl_constant * refl_constant) = (mk_inspect_pack_pair "_comp")


let fstar_refl_inspect_comp : refl_constant = (match (uu___105) with
| (fstar_refl_inspect_comp, fstar_refl_pack_comp) -> begin
fstar_refl_inspect_comp
end)


let fstar_refl_pack_comp : refl_constant = (match (uu___105) with
| (fstar_refl_inspect_comp1, fstar_refl_pack_comp) -> begin
fstar_refl_pack_comp
end)


let uu___112 : (refl_constant * refl_constant) = (mk_inspect_pack_pair "_sigelt")


let fstar_refl_inspect_sigelt : refl_constant = (match (uu___112) with
| (fstar_refl_inspect_sigelt, fstar_refl_pack_sigelt) -> begin
fstar_refl_inspect_sigelt
end)


let fstar_refl_pack_sigelt : refl_constant = (match (uu___112) with
| (fstar_refl_inspect_sigelt1, fstar_refl_pack_sigelt) -> begin
fstar_refl_pack_sigelt
end)


let fstar_refl_env : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "env")


let fstar_refl_env_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "env")


let fstar_refl_bv : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "bv")


let fstar_refl_bv_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "bv")


let fstar_refl_fv : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "fv")


let fstar_refl_fv_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "fv")


let fstar_refl_comp : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "comp")


let fstar_refl_comp_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "comp")


let fstar_refl_binder : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "binder")


let fstar_refl_binder_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "binder")


let fstar_refl_sigelt : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "sigelt")


let fstar_refl_sigelt_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "sigelt")


let fstar_refl_term : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "term")


let fstar_refl_term_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "term")


let fstar_refl_ident : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "ident")


let fstar_refl_ident_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "ident")


let fstar_refl_univ_name : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "univ_name")


let fstar_refl_univ_name_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "univ_name")


let fstar_refl_optionstate : FStar_Syntax_Syntax.term = (mk_refl_types_lid_as_term "optionstate")


let fstar_refl_optionstate_fv : FStar_Syntax_Syntax.fv = (mk_refl_types_lid_as_fv "optionstate")


let fstar_refl_aqualv : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "aqualv")


let fstar_refl_aqualv_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "aqualv")


let fstar_refl_comp_view : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "comp_view")


let fstar_refl_comp_view_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "comp_view")


let fstar_refl_term_view : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "term_view")


let fstar_refl_term_view_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "term_view")


let fstar_refl_pattern : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "pattern")


let fstar_refl_pattern_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "pattern")


let fstar_refl_branch : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "branch")


let fstar_refl_branch_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "branch")


let fstar_refl_bv_view : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "bv_view")


let fstar_refl_bv_view_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "bv_view")


let fstar_refl_vconst : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "vconst")


let fstar_refl_vconst_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "vconst")


let fstar_refl_sigelt_view : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "sigelt_view")


let fstar_refl_sigelt_view_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "sigelt_view")


let fstar_refl_exp : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "exp")


let fstar_refl_exp_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "exp")


let fstar_refl_qualifier : FStar_Syntax_Syntax.term = (mk_refl_data_lid_as_term "qualifier")


let fstar_refl_qualifier_fv : FStar_Syntax_Syntax.fv = (mk_refl_data_lid_as_fv "qualifier")


let ref_Mk_bv : refl_constant = (

let lid = (fstar_refl_data_lid "Mkbv_view")
in (

let attr = (

let uu____2315 = (

let uu____2322 = (fstar_refl_data_lid "bv_view")
in (

let uu____2324 = (

let uu____2327 = (FStar_Ident.mk_ident (("bv_ppname"), (FStar_Range.dummyRange)))
in (

let uu____2330 = (

let uu____2333 = (FStar_Ident.mk_ident (("bv_index"), (FStar_Range.dummyRange)))
in (

let uu____2336 = (

let uu____2339 = (FStar_Ident.mk_ident (("bv_sort"), (FStar_Range.dummyRange)))
in (uu____2339)::[])
in (uu____2333)::uu____2336))
in (uu____2327)::uu____2330))
in ((uu____2322), (uu____2324))))
in FStar_Syntax_Syntax.Record_ctor (uu____2315))
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (attr)))
in (

let uu____2345 = (FStar_Syntax_Syntax.fv_to_tm fv)
in {lid = lid; fv = fv; t = uu____2345}))))


let ref_Q_Explicit : refl_constant = (fstar_refl_data_const "Q_Explicit")


let ref_Q_Implicit : refl_constant = (fstar_refl_data_const "Q_Implicit")


let ref_Q_Meta : refl_constant = (fstar_refl_data_const "Q_Meta")


let ref_C_Unit : refl_constant = (fstar_refl_data_const "C_Unit")


let ref_C_True : refl_constant = (fstar_refl_data_const "C_True")


let ref_C_False : refl_constant = (fstar_refl_data_const "C_False")


let ref_C_Int : refl_constant = (fstar_refl_data_const "C_Int")


let ref_C_String : refl_constant = (fstar_refl_data_const "C_String")


let ref_C_Range : refl_constant = (fstar_refl_data_const "C_Range")


let ref_C_Reify : refl_constant = (fstar_refl_data_const "C_Reify")


let ref_C_Reflect : refl_constant = (fstar_refl_data_const "C_Reflect")


let ref_Pat_Constant : refl_constant = (fstar_refl_data_const "Pat_Constant")


let ref_Pat_Cons : refl_constant = (fstar_refl_data_const "Pat_Cons")


let ref_Pat_Var : refl_constant = (fstar_refl_data_const "Pat_Var")


let ref_Pat_Wild : refl_constant = (fstar_refl_data_const "Pat_Wild")


let ref_Pat_Dot_Term : refl_constant = (fstar_refl_data_const "Pat_Dot_Term")


let ref_Tv_Var : refl_constant = (fstar_refl_data_const "Tv_Var")


let ref_Tv_BVar : refl_constant = (fstar_refl_data_const "Tv_BVar")


let ref_Tv_FVar : refl_constant = (fstar_refl_data_const "Tv_FVar")


let ref_Tv_App : refl_constant = (fstar_refl_data_const "Tv_App")


let ref_Tv_Abs : refl_constant = (fstar_refl_data_const "Tv_Abs")


let ref_Tv_Arrow : refl_constant = (fstar_refl_data_const "Tv_Arrow")


let ref_Tv_Type : refl_constant = (fstar_refl_data_const "Tv_Type")


let ref_Tv_Refine : refl_constant = (fstar_refl_data_const "Tv_Refine")


let ref_Tv_Const : refl_constant = (fstar_refl_data_const "Tv_Const")


let ref_Tv_Uvar : refl_constant = (fstar_refl_data_const "Tv_Uvar")


let ref_Tv_Let : refl_constant = (fstar_refl_data_const "Tv_Let")


let ref_Tv_Match : refl_constant = (fstar_refl_data_const "Tv_Match")


let ref_Tv_AscT : refl_constant = (fstar_refl_data_const "Tv_AscribedT")


let ref_Tv_AscC : refl_constant = (fstar_refl_data_const "Tv_AscribedC")


let ref_Tv_Unknown : refl_constant = (fstar_refl_data_const "Tv_Unknown")


let ref_C_Total : refl_constant = (fstar_refl_data_const "C_Total")


let ref_C_Lemma : refl_constant = (fstar_refl_data_const "C_Lemma")


let ref_C_Unknown : refl_constant = (fstar_refl_data_const "C_Unknown")


let ref_Sg_Let : refl_constant = (fstar_refl_data_const "Sg_Let")


let ref_Sg_Inductive : refl_constant = (fstar_refl_data_const "Sg_Inductive")


let ref_Sg_Constructor : refl_constant = (fstar_refl_data_const "Sg_Constructor")


let ref_Unk : refl_constant = (fstar_refl_data_const "Unk")


let ref_qual_Assumption : refl_constant = (fstar_refl_data_const "Assumption")


let ref_qual_New : refl_constant = (fstar_refl_data_const "New")


let ref_qual_Private : refl_constant = (fstar_refl_data_const "Private")


let ref_qual_Unfold_for_unification_and_vcgen : refl_constant = (fstar_refl_data_const "Unfold_for_unification_and_vcgen")


let ref_qual_Visible_default : refl_constant = (fstar_refl_data_const "Visible_default")


let ref_qual_Irreducible : refl_constant = (fstar_refl_data_const "Irreducible")


let ref_qual_Abstract : refl_constant = (fstar_refl_data_const "Abstract")


let ref_qual_Inline_for_extraction : refl_constant = (fstar_refl_data_const "Inline_for_extraction")


let ref_qual_NoExtract : refl_constant = (fstar_refl_data_const "NoExtract")


let ref_qual_Noeq : refl_constant = (fstar_refl_data_const "Noeq")


let ref_qual_Unopteq : refl_constant = (fstar_refl_data_const "Unopteq")


let ref_qual_TotalEffect : refl_constant = (fstar_refl_data_const "TotalEffect")


let ref_qual_Logic : refl_constant = (fstar_refl_data_const "Logic")


let ref_qual_Reifiable : refl_constant = (fstar_refl_data_const "Reifiable")


let ref_qual_Reflectable : refl_constant = (fstar_refl_data_const "Reflectable")


let ref_qual_Discriminator : refl_constant = (fstar_refl_data_const "Discriminator")


let ref_qual_Projector : refl_constant = (fstar_refl_data_const "Projector")


let ref_qual_RecordType : refl_constant = (fstar_refl_data_const "RecordType")


let ref_qual_RecordConstructor : refl_constant = (fstar_refl_data_const "RecordConstructor")


let ref_qual_Action : refl_constant = (fstar_refl_data_const "Action")


let ref_qual_ExceptionConstructor : refl_constant = (fstar_refl_data_const "ExceptionConstructor")


let ref_qual_HasMaskedEffect : refl_constant = (fstar_refl_data_const "HasMaskedEffect")


let ref_qual_Effect : refl_constant = (fstar_refl_data_const "Effect")


let ref_qual_OnlyName : refl_constant = (fstar_refl_data_const "OnlyName")


let ref_E_Unit : refl_constant = (fstar_refl_data_const "Unit")


let ref_E_Var : refl_constant = (fstar_refl_data_const "Var")


let ref_E_Mult : refl_constant = (fstar_refl_data_const "Mult")


let t_exp : FStar_Syntax_Syntax.term = (

let uu____2477 = (FStar_Ident.lid_of_path (("FStar")::("Reflection")::("Data")::("exp")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.tconst uu____2477))


let ord_Lt_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Lt")::[]) FStar_Range.dummyRange)


let ord_Eq_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Eq")::[]) FStar_Range.dummyRange)


let ord_Gt_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("FStar")::("Order")::("Gt")::[]) FStar_Range.dummyRange)


let ord_Lt : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Lt_lid)


let ord_Eq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Eq_lid)


let ord_Gt : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr ord_Gt_lid)


let ord_Lt_fv : FStar_Syntax_Syntax.fv = (FStar_Syntax_Syntax.lid_as_fv ord_Lt_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let ord_Eq_fv : FStar_Syntax_Syntax.fv = (FStar_Syntax_Syntax.lid_as_fv ord_Eq_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let ord_Gt_fv : FStar_Syntax_Syntax.fv = (FStar_Syntax_Syntax.lid_as_fv ord_Gt_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


type decls =
FStar_Syntax_Syntax.sigelt Prims.list




