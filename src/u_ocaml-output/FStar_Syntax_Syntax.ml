
open Prims
type ('a, 't) withinfo_t =
{v : 'a; ty : 't; p : FStar_Range.range}


type 't var =
(FStar_Ident.lident, 't) withinfo_t


type sconst =
FStar_Const.sconst

type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string Prims.option


let uu___is_SetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
true
end
| uu____78 -> begin
false
end))


let __proj__SetOptions__item___0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
_0
end))


let uu___is_ResetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
true
end
| uu____91 -> begin
false
end))


let __proj__ResetOptions__item___0 : pragma  ->  Prims.string Prims.option = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
_0
end))


type 'a memo =
'a Prims.option FStar_ST.ref

type arg_qualifier =
| Implicit of Prims.bool
| Equality


let uu___is_Implicit : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_0) -> begin
true
end
| uu____112 -> begin
false
end))


let __proj__Implicit__item___0 : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_0) -> begin
_0
end))


let uu___is_Equality : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equality -> begin
true
end
| uu____123 -> begin
false
end))


type aqual =
arg_qualifier Prims.option

type universe =
| U_zero
| U_succ of universe
| U_max of universe Prims.list
| U_bvar of Prims.int
| U_name of FStar_Ident.ident
| U_unif of universe Prims.option FStar_Unionfind.uvar
| U_unknown


let uu___is_U_zero : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_zero -> begin
true
end
| uu____146 -> begin
false
end))


let uu___is_U_succ : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_succ (_0) -> begin
true
end
| uu____151 -> begin
false
end))


let __proj__U_succ__item___0 : universe  ->  universe = (fun projectee -> (match (projectee) with
| U_succ (_0) -> begin
_0
end))


let uu___is_U_max : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_max (_0) -> begin
true
end
| uu____164 -> begin
false
end))


let __proj__U_max__item___0 : universe  ->  universe Prims.list = (fun projectee -> (match (projectee) with
| U_max (_0) -> begin
_0
end))


let uu___is_U_bvar : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_bvar (_0) -> begin
true
end
| uu____179 -> begin
false
end))


let __proj__U_bvar__item___0 : universe  ->  Prims.int = (fun projectee -> (match (projectee) with
| U_bvar (_0) -> begin
_0
end))


let uu___is_U_name : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_name (_0) -> begin
true
end
| uu____191 -> begin
false
end))


let __proj__U_name__item___0 : universe  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| U_name (_0) -> begin
_0
end))


let uu___is_U_unif : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_unif (_0) -> begin
true
end
| uu____205 -> begin
false
end))


let __proj__U_unif__item___0 : universe  ->  universe Prims.option FStar_Unionfind.uvar = (fun projectee -> (match (projectee) with
| U_unif (_0) -> begin
_0
end))


let uu___is_U_unknown : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_unknown -> begin
true
end
| uu____222 -> begin
false
end))


type univ_name =
FStar_Ident.ident


type universe_uvar =
universe Prims.option FStar_Unionfind.uvar


type univ_names =
univ_name Prims.list


type universes =
universe Prims.list


type monad_name =
FStar_Ident.lident

type delta_depth =
| Delta_constant
| Delta_defined_at_level of Prims.int
| Delta_equational
| Delta_abstract of delta_depth


let uu___is_Delta_constant : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_constant -> begin
true
end
| uu____236 -> begin
false
end))


let uu___is_Delta_defined_at_level : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_defined_at_level (_0) -> begin
true
end
| uu____241 -> begin
false
end))


let __proj__Delta_defined_at_level__item___0 : delta_depth  ->  Prims.int = (fun projectee -> (match (projectee) with
| Delta_defined_at_level (_0) -> begin
_0
end))


let uu___is_Delta_equational : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_equational -> begin
true
end
| uu____252 -> begin
false
end))


let uu___is_Delta_abstract : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_abstract (_0) -> begin
true
end
| uu____257 -> begin
false
end))


let __proj__Delta_abstract__item___0 : delta_depth  ->  delta_depth = (fun projectee -> (match (projectee) with
| Delta_abstract (_0) -> begin
_0
end))

type term' =
| Tm_bvar of bv
| Tm_name of bv
| Tm_fvar of fv
| Tm_uinst of ((term', term') syntax * universes)
| Tm_constant of sconst
| Tm_type of universe
| Tm_abs of ((bv * aqual) Prims.list * (term', term') syntax * (lcomp, (FStar_Ident.lident * cflags Prims.list)) FStar_Util.either Prims.option)
| Tm_arrow of ((bv * aqual) Prims.list * (comp', Prims.unit) syntax)
| Tm_refine of (bv * (term', term') syntax)
| Tm_app of ((term', term') syntax * ((term', term') syntax * aqual) Prims.list)
| Tm_match of ((term', term') syntax * ((pat', term') withinfo_t * (term', term') syntax Prims.option * (term', term') syntax) Prims.list)
| Tm_ascribed of ((term', term') syntax * ((term', term') syntax, (comp', Prims.unit) syntax) FStar_Util.either * FStar_Ident.lident Prims.option)
| Tm_let of ((Prims.bool * letbinding Prims.list) * (term', term') syntax)
| Tm_uvar of ((term', term') syntax uvar_basis FStar_Unionfind.uvar * (term', term') syntax)
| Tm_delayed of ((((term', term') syntax * (subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)), Prims.unit  ->  (term', term') syntax) FStar_Util.either * (term', term') syntax memo)
| Tm_meta of ((term', term') syntax * metadata)
| Tm_unknown 
 and pat' =
| Pat_constant of sconst
| Pat_disj of (pat', term') withinfo_t Prims.list
| Pat_cons of (fv * ((pat', term') withinfo_t * Prims.bool) Prims.list)
| Pat_var of bv
| Pat_wild of bv
| Pat_dot_term of (bv * (term', term') syntax) 
 and letbinding =
{lbname : (bv, fv) FStar_Util.either; lbunivs : univ_name Prims.list; lbtyp : (term', term') syntax; lbeff : FStar_Ident.lident; lbdef : (term', term') syntax} 
 and comp_typ =
{comp_univs : universes; effect_name : FStar_Ident.lident; result_typ : (term', term') syntax; effect_args : ((term', term') syntax * aqual) Prims.list; flags : cflags Prims.list} 
 and comp' =
| Total of ((term', term') syntax * universe Prims.option)
| GTotal of ((term', term') syntax * universe Prims.option)
| Comp of comp_typ 
 and cflags =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| LEMMA
| CPS
| DECREASES of (term', term') syntax 
 and metadata =
| Meta_pattern of ((term', term') syntax * aqual) Prims.list Prims.list
| Meta_named of FStar_Ident.lident
| Meta_labeled of (Prims.string * FStar_Range.range * Prims.bool)
| Meta_desugared of meta_source_info
| Meta_monadic of (monad_name * (term', term') syntax)
| Meta_monadic_lift of (monad_name * monad_name * (term', term') syntax) 
 and 'a uvar_basis =
| Uvar
| Fixed of 'a 
 and meta_source_info =
| Data_app
| Sequence
| Primop
| Masked_effect
| Meta_smt_pat
| Mutable_alloc
| Mutable_rval 
 and fv_qual =
| Data_ctor
| Record_projector of (FStar_Ident.lident * FStar_Ident.ident)
| Record_ctor of (FStar_Ident.lident * FStar_Ident.ident Prims.list) 
 and subst_elt =
| DB of (Prims.int * bv)
| NM of (bv * Prims.int)
| NT of (bv * (term', term') syntax)
| UN of (Prims.int * universe)
| UD of (univ_name * Prims.int) 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : FStar_Range.range; vars : free_vars memo} 
 and bv =
{ppname : FStar_Ident.ident; index : Prims.int; sort : (term', term') syntax} 
 and fv =
{fv_name : (term', term') syntax var; fv_delta : delta_depth; fv_qual : fv_qual Prims.option} 
 and free_vars =
{free_names : bv FStar_Util.set; free_uvars : ((term', term') syntax uvar_basis FStar_Unionfind.uvar * (term', term') syntax) FStar_Util.set; free_univs : universe_uvar FStar_Util.set; free_univ_names : univ_name FStar_Util.fifo_set} 
 and lcomp =
{eff_name : FStar_Ident.lident; res_typ : (term', term') syntax; cflags : cflags Prims.list; comp : Prims.unit  ->  (comp', Prims.unit) syntax}


let uu___is_Tm_bvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_bvar (_0) -> begin
true
end
| uu____697 -> begin
false
end))


let __proj__Tm_bvar__item___0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_bvar (_0) -> begin
_0
end))


let uu___is_Tm_name : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_name (_0) -> begin
true
end
| uu____709 -> begin
false
end))


let __proj__Tm_name__item___0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_name (_0) -> begin
_0
end))


let uu___is_Tm_fvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_fvar (_0) -> begin
true
end
| uu____721 -> begin
false
end))


let __proj__Tm_fvar__item___0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| Tm_fvar (_0) -> begin
_0
end))


let uu___is_Tm_uinst : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_uinst (_0) -> begin
true
end
| uu____737 -> begin
false
end))


let __proj__Tm_uinst__item___0 : term'  ->  ((term', term') syntax * universes) = (fun projectee -> (match (projectee) with
| Tm_uinst (_0) -> begin
_0
end))


let uu___is_Tm_constant : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_constant (_0) -> begin
true
end
| uu____761 -> begin
false
end))


let __proj__Tm_constant__item___0 : term'  ->  sconst = (fun projectee -> (match (projectee) with
| Tm_constant (_0) -> begin
_0
end))


let uu___is_Tm_type : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_type (_0) -> begin
true
end
| uu____773 -> begin
false
end))


let __proj__Tm_type__item___0 : term'  ->  universe = (fun projectee -> (match (projectee) with
| Tm_type (_0) -> begin
_0
end))


let uu___is_Tm_abs : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_abs (_0) -> begin
true
end
| uu____799 -> begin
false
end))


let __proj__Tm_abs__item___0 : term'  ->  ((bv * aqual) Prims.list * (term', term') syntax * (lcomp, (FStar_Ident.lident * cflags Prims.list)) FStar_Util.either Prims.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_0) -> begin
_0
end))


let uu___is_Tm_arrow : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_arrow (_0) -> begin
true
end
| uu____860 -> begin
false
end))


let __proj__Tm_arrow__item___0 : term'  ->  ((bv * aqual) Prims.list * (comp', Prims.unit) syntax) = (fun projectee -> (match (projectee) with
| Tm_arrow (_0) -> begin
_0
end))


let uu___is_Tm_refine : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_refine (_0) -> begin
true
end
| uu____897 -> begin
false
end))


let __proj__Tm_refine__item___0 : term'  ->  (bv * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Tm_refine (_0) -> begin
_0
end))


let uu___is_Tm_app : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_app (_0) -> begin
true
end
| uu____930 -> begin
false
end))


let __proj__Tm_app__item___0 : term'  ->  ((term', term') syntax * ((term', term') syntax * aqual) Prims.list) = (fun projectee -> (match (projectee) with
| Tm_app (_0) -> begin
_0
end))


let uu___is_Tm_match : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_match (_0) -> begin
true
end
| uu____984 -> begin
false
end))


let __proj__Tm_match__item___0 : term'  ->  ((term', term') syntax * ((pat', term') withinfo_t * (term', term') syntax Prims.option * (term', term') syntax) Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_0) -> begin
_0
end))


let uu___is_Tm_ascribed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_ascribed (_0) -> begin
true
end
| uu____1053 -> begin
false
end))


let __proj__Tm_ascribed__item___0 : term'  ->  ((term', term') syntax * ((term', term') syntax, (comp', Prims.unit) syntax) FStar_Util.either * FStar_Ident.lident Prims.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_0) -> begin
_0
end))


let uu___is_Tm_let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_let (_0) -> begin
true
end
| uu____1108 -> begin
false
end))


let __proj__Tm_let__item___0 : term'  ->  ((Prims.bool * letbinding Prims.list) * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Tm_let (_0) -> begin
_0
end))


let uu___is_Tm_uvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_uvar (_0) -> begin
true
end
| uu____1149 -> begin
false
end))


let __proj__Tm_uvar__item___0 : term'  ->  ((term', term') syntax uvar_basis FStar_Unionfind.uvar * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Tm_uvar (_0) -> begin
_0
end))


let uu___is_Tm_delayed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_delayed (_0) -> begin
true
end
| uu____1205 -> begin
false
end))


let __proj__Tm_delayed__item___0 : term'  ->  ((((term', term') syntax * (subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)), Prims.unit  ->  (term', term') syntax) FStar_Util.either * (term', term') syntax memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_0) -> begin
_0
end))


let uu___is_Tm_meta : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_meta (_0) -> begin
true
end
| uu____1281 -> begin
false
end))


let __proj__Tm_meta__item___0 : term'  ->  ((term', term') syntax * metadata) = (fun projectee -> (match (projectee) with
| Tm_meta (_0) -> begin
_0
end))


let uu___is_Tm_unknown : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_unknown -> begin
true
end
| uu____1304 -> begin
false
end))


let uu___is_Pat_constant : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_constant (_0) -> begin
true
end
| uu____1309 -> begin
false
end))


let __proj__Pat_constant__item___0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_0) -> begin
_0
end))


let uu___is_Pat_disj : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_disj (_0) -> begin
true
end
| uu____1324 -> begin
false
end))


let __proj__Pat_disj__item___0 : pat'  ->  (pat', term') withinfo_t Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_0) -> begin
_0
end))


let uu___is_Pat_cons : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_cons (_0) -> begin
true
end
| uu____1352 -> begin
false
end))


let __proj__Pat_cons__item___0 : pat'  ->  (fv * ((pat', term') withinfo_t * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_0) -> begin
_0
end))


let uu___is_Pat_var : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_var (_0) -> begin
true
end
| uu____1385 -> begin
false
end))


let __proj__Pat_var__item___0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_var (_0) -> begin
_0
end))


let uu___is_Pat_wild : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_wild (_0) -> begin
true
end
| uu____1397 -> begin
false
end))


let __proj__Pat_wild__item___0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_wild (_0) -> begin
_0
end))


let uu___is_Pat_dot_term : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_dot_term (_0) -> begin
true
end
| uu____1413 -> begin
false
end))


let __proj__Pat_dot_term__item___0 : pat'  ->  (bv * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_0) -> begin
_0
end))


let uu___is_Total : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Total (_0) -> begin
true
end
| uu____1512 -> begin
false
end))


let __proj__Total__item___0 : comp'  ->  ((term', term') syntax * universe Prims.option) = (fun projectee -> (match (projectee) with
| Total (_0) -> begin
_0
end))


let uu___is_GTotal : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTotal (_0) -> begin
true
end
| uu____1544 -> begin
false
end))


let __proj__GTotal__item___0 : comp'  ->  ((term', term') syntax * universe Prims.option) = (fun projectee -> (match (projectee) with
| GTotal (_0) -> begin
_0
end))


let uu___is_Comp : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
true
end
| uu____1571 -> begin
false
end))


let __proj__Comp__item___0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
_0
end))


let uu___is_TOTAL : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TOTAL -> begin
true
end
| uu____1582 -> begin
false
end))


let uu___is_MLEFFECT : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLEFFECT -> begin
true
end
| uu____1586 -> begin
false
end))


let uu___is_RETURN : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RETURN -> begin
true
end
| uu____1590 -> begin
false
end))


let uu___is_PARTIAL_RETURN : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PARTIAL_RETURN -> begin
true
end
| uu____1594 -> begin
false
end))


let uu___is_SOMETRIVIAL : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SOMETRIVIAL -> begin
true
end
| uu____1598 -> begin
false
end))


let uu___is_LEMMA : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LEMMA -> begin
true
end
| uu____1602 -> begin
false
end))


let uu___is_CPS : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPS -> begin
true
end
| uu____1606 -> begin
false
end))


let uu___is_DECREASES : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
true
end
| uu____1613 -> begin
false
end))


let __proj__DECREASES__item___0 : cflags  ->  (term', term') syntax = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
_0
end))


let uu___is_Meta_pattern : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_pattern (_0) -> begin
true
end
| uu____1637 -> begin
false
end))


let __proj__Meta_pattern__item___0 : metadata  ->  ((term', term') syntax * aqual) Prims.list Prims.list = (fun projectee -> (match (projectee) with
| Meta_pattern (_0) -> begin
_0
end))


let uu___is_Meta_named : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_named (_0) -> begin
true
end
| uu____1667 -> begin
false
end))


let __proj__Meta_named__item___0 : metadata  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Meta_named (_0) -> begin
_0
end))


let uu___is_Meta_labeled : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_labeled (_0) -> begin
true
end
| uu____1682 -> begin
false
end))


let __proj__Meta_labeled__item___0 : metadata  ->  (Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_0) -> begin
_0
end))


let uu___is_Meta_desugared : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_desugared (_0) -> begin
true
end
| uu____1703 -> begin
false
end))


let __proj__Meta_desugared__item___0 : metadata  ->  meta_source_info = (fun projectee -> (match (projectee) with
| Meta_desugared (_0) -> begin
_0
end))


let uu___is_Meta_monadic : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_monadic (_0) -> begin
true
end
| uu____1719 -> begin
false
end))


let __proj__Meta_monadic__item___0 : metadata  ->  (monad_name * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Meta_monadic (_0) -> begin
_0
end))


let uu___is_Meta_monadic_lift : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_monadic_lift (_0) -> begin
true
end
| uu____1748 -> begin
false
end))


let __proj__Meta_monadic_lift__item___0 : metadata  ->  (monad_name * monad_name * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Meta_monadic_lift (_0) -> begin
_0
end))


let uu___is_Uvar = (fun projectee -> (match (projectee) with
| Uvar -> begin
true
end
| uu____1780 -> begin
false
end))


let uu___is_Fixed = (fun projectee -> (match (projectee) with
| Fixed (_0) -> begin
true
end
| uu____1792 -> begin
false
end))


let __proj__Fixed__item___0 = (fun projectee -> (match (projectee) with
| Fixed (_0) -> begin
_0
end))


let uu___is_Data_app : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Data_app -> begin
true
end
| uu____1810 -> begin
false
end))


let uu___is_Sequence : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sequence -> begin
true
end
| uu____1814 -> begin
false
end))


let uu___is_Primop : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primop -> begin
true
end
| uu____1818 -> begin
false
end))


let uu___is_Masked_effect : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Masked_effect -> begin
true
end
| uu____1822 -> begin
false
end))


let uu___is_Meta_smt_pat : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_smt_pat -> begin
true
end
| uu____1826 -> begin
false
end))


let uu___is_Mutable_alloc : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable_alloc -> begin
true
end
| uu____1830 -> begin
false
end))


let uu___is_Mutable_rval : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable_rval -> begin
true
end
| uu____1834 -> begin
false
end))


let uu___is_Data_ctor : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Data_ctor -> begin
true
end
| uu____1838 -> begin
false
end))


let uu___is_Record_projector : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record_projector (_0) -> begin
true
end
| uu____1845 -> begin
false
end))


let __proj__Record_projector__item___0 : fv_qual  ->  (FStar_Ident.lident * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Record_projector (_0) -> begin
_0
end))


let uu___is_Record_ctor : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record_ctor (_0) -> begin
true
end
| uu____1866 -> begin
false
end))


let __proj__Record_ctor__item___0 : fv_qual  ->  (FStar_Ident.lident * FStar_Ident.ident Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_0) -> begin
_0
end))


let uu___is_DB : subst_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DB (_0) -> begin
true
end
| uu____1889 -> begin
false
end))


let __proj__DB__item___0 : subst_elt  ->  (Prims.int * bv) = (fun projectee -> (match (projectee) with
| DB (_0) -> begin
_0
end))


let uu___is_NM : subst_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NM (_0) -> begin
true
end
| uu____1909 -> begin
false
end))


let __proj__NM__item___0 : subst_elt  ->  (bv * Prims.int) = (fun projectee -> (match (projectee) with
| NM (_0) -> begin
_0
end))


let uu___is_NT : subst_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NT (_0) -> begin
true
end
| uu____1931 -> begin
false
end))


let __proj__NT__item___0 : subst_elt  ->  (bv * (term', term') syntax) = (fun projectee -> (match (projectee) with
| NT (_0) -> begin
_0
end))


let uu___is_UN : subst_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UN (_0) -> begin
true
end
| uu____1957 -> begin
false
end))


let __proj__UN__item___0 : subst_elt  ->  (Prims.int * universe) = (fun projectee -> (match (projectee) with
| UN (_0) -> begin
_0
end))


let uu___is_UD : subst_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UD (_0) -> begin
true
end
| uu____1977 -> begin
false
end))


let __proj__UD__item___0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_0) -> begin
_0
end))


type pat =
(pat', term') withinfo_t


type term =
(term', term') syntax


type branch =
((pat', term') withinfo_t * (term', term') syntax Prims.option * (term', term') syntax)


type typ =
(term', term') syntax


type comp =
(comp', Prims.unit) syntax


type arg =
((term', term') syntax * aqual)


type args =
((term', term') syntax * aqual) Prims.list


type binder =
(bv * aqual)


type binders =
(bv * aqual) Prims.list


type uvar =
(term', term') syntax uvar_basis FStar_Unionfind.uvar


type lbname =
(bv, fv) FStar_Util.either


type letbindings =
(Prims.bool * letbinding Prims.list)


type subst_ts =
(subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)


type freenames =
bv FStar_Util.set


type uvars =
((term', term') syntax uvar_basis FStar_Unionfind.uvar * (term', term') syntax) FStar_Util.set


type residual_comp =
(FStar_Ident.lident * cflags Prims.list)


type tscheme =
(univ_name Prims.list * typ)


type freenames_l =
bv Prims.list


type formula =
typ


type formulae =
typ Prims.list

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
| Reflectable of FStar_Ident.lident
| Discriminator of FStar_Ident.lident
| Projector of (FStar_Ident.lident * FStar_Ident.ident)
| RecordType of (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list)
| RecordConstructor of (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list)
| Action of FStar_Ident.lident
| ExceptionConstructor
| HasMaskedEffect
| Effect
| OnlyName


let uu___is_Assumption : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumption -> begin
true
end
| uu____2268 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____2272 -> begin
false
end))


let uu___is_Private : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____2276 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____2280 -> begin
false
end))


let uu___is_Visible_default : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible_default -> begin
true
end
| uu____2284 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____2288 -> begin
false
end))


let uu___is_Abstract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____2292 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____2296 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____2300 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____2304 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____2308 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____2312 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____2316 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____2320 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable (_0) -> begin
true
end
| uu____2325 -> begin
false
end))


let __proj__Reflectable__item___0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Reflectable (_0) -> begin
_0
end))


let uu___is_Discriminator : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Discriminator (_0) -> begin
true
end
| uu____2337 -> begin
false
end))


let __proj__Discriminator__item___0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Discriminator (_0) -> begin
_0
end))


let uu___is_Projector : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Projector (_0) -> begin
true
end
| uu____2351 -> begin
false
end))


let __proj__Projector__item___0 : qualifier  ->  (FStar_Ident.lident * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_0) -> begin
_0
end))


let uu___is_RecordType : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RecordType (_0) -> begin
true
end
| uu____2373 -> begin
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
| uu____2401 -> begin
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
| uu____2425 -> begin
false
end))


let __proj__Action__item___0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Action (_0) -> begin
_0
end))


let uu___is_ExceptionConstructor : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ExceptionConstructor -> begin
true
end
| uu____2436 -> begin
false
end))


let uu___is_HasMaskedEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HasMaskedEffect -> begin
true
end
| uu____2440 -> begin
false
end))


let uu___is_Effect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect -> begin
true
end
| uu____2444 -> begin
false
end))


let uu___is_OnlyName : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OnlyName -> begin
true
end
| uu____2448 -> begin
false
end))


type attribute =
term


type tycon =
(FStar_Ident.lident * binders * typ)

type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}

type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift_wp : tscheme Prims.option; lift : tscheme Prims.option}

type action =
{action_name : FStar_Ident.lident; action_unqualified_name : FStar_Ident.ident; action_univs : univ_names; action_defn : term; action_typ : typ}

type eff_decl =
{qualifiers : qualifier Prims.list; cattributes : cflags Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret_wp : tscheme; bind_wp : tscheme; if_then_else : tscheme; ite_wp : tscheme; stronger : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme; repr : term; return_repr : tscheme; bind_repr : tscheme; actions : action Prims.list} 
 and sigelt =
| Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range)
| Sig_bundle of (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_datacon of (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_declare_typ of (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range)
| Sig_let of (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list * attribute Prims.list)
| Sig_main of (term * FStar_Range.range)
| Sig_assume of (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range)
| Sig_new_effect of (eff_decl * FStar_Range.range)
| Sig_new_effect_for_free of (eff_decl * FStar_Range.range)
| Sig_sub_effect of (sub_eff * FStar_Range.range)
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * cflags Prims.list * FStar_Range.range)
| Sig_pragma of (pragma * FStar_Range.range)


let uu___is_Sig_inductive_typ : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_0) -> begin
true
end
| uu____2808 -> begin
false
end))


let __proj__Sig_inductive_typ__item___0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_0) -> begin
_0
end))


let uu___is_Sig_bundle : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_bundle (_0) -> begin
true
end
| uu____2860 -> begin
false
end))


let __proj__Sig_bundle__item___0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_0) -> begin
_0
end))


let uu___is_Sig_datacon : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_datacon (_0) -> begin
true
end
| uu____2903 -> begin
false
end))


let __proj__Sig_datacon__item___0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_0) -> begin
_0
end))


let uu___is_Sig_declare_typ : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_0) -> begin
true
end
| uu____2951 -> begin
false
end))


let __proj__Sig_declare_typ__item___0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_0) -> begin
_0
end))


let uu___is_Sig_let : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_let (_0) -> begin
true
end
| uu____2989 -> begin
false
end))


let __proj__Sig_let__item___0 : sigelt  ->  (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list * attribute Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_0) -> begin
_0
end))


let uu___is_Sig_main : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_main (_0) -> begin
true
end
| uu____3027 -> begin
false
end))


let __proj__Sig_main__item___0 : sigelt  ->  (term * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_0) -> begin
_0
end))


let uu___is_Sig_assume : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_assume (_0) -> begin
true
end
| uu____3050 -> begin
false
end))


let __proj__Sig_assume__item___0 : sigelt  ->  (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_0) -> begin
_0
end))


let uu___is_Sig_new_effect : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_new_effect (_0) -> begin
true
end
| uu____3079 -> begin
false
end))


let __proj__Sig_new_effect__item___0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_0) -> begin
_0
end))


let uu___is_Sig_new_effect_for_free : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_new_effect_for_free (_0) -> begin
true
end
| uu____3099 -> begin
false
end))


let __proj__Sig_new_effect_for_free__item___0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect_for_free (_0) -> begin
_0
end))


let uu___is_Sig_sub_effect : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_0) -> begin
true
end
| uu____3119 -> begin
false
end))


let __proj__Sig_sub_effect__item___0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_0) -> begin
_0
end))


let uu___is_Sig_effect_abbrev : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_0) -> begin
true
end
| uu____3146 -> begin
false
end))


let __proj__Sig_effect_abbrev__item___0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * cflags Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_0) -> begin
_0
end))


let uu___is_Sig_pragma : sigelt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_pragma (_0) -> begin
true
end
| uu____3187 -> begin
false
end))


let __proj__Sig_pragma__item___0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_0) -> begin
_0
end))


type sigelts =
sigelt Prims.list

type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}


type path =
Prims.string Prims.list


type subst_t =
subst_elt Prims.list


type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax


type mk_t =
(term', term') mk_t_a


let contains_reflectable : qualifier Prims.list  ->  Prims.bool = (fun l -> (FStar_Util.for_some (fun uu___89_3248 -> (match (uu___89_3248) with
| Reflectable (uu____3249) -> begin
true
end
| uu____3250 -> begin
false
end)) l))


let withinfo = (fun v s r -> {v = v; ty = s; p = r})


let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))


let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))


let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (

let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(x.index - y.index)
end
| uu____3301 -> begin
i
end)))


let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.fv_name.v)
end))


let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)


let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (

let uu___96_3320 = x
in {ppname = (FStar_Ident.mk_ident ((x.ppname.FStar_Ident.idText), (r))); index = uu___96_3320.index; sort = uu___96_3320.sort}))


let syn = (fun p k f -> (f k p))


let mk_fvs = (fun uu____3361 -> (FStar_Util.mk_ref None))


let mk_uvs = (fun uu____3373 -> (FStar_Util.mk_ref None))


let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun uu____3379 -> (FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText)))))


let new_uv_set : Prims.unit  ->  uvars = (fun uu____3384 -> (FStar_Util.new_set (fun uu____3393 uu____3394 -> (match (((uu____3393), (uu____3394))) with
| ((x, uu____3428), (y, uu____3430)) -> begin
(let _0_24 = (FStar_Unionfind.uvar_id x)
in (let _0_23 = (FStar_Unionfind.uvar_id y)
in (_0_24 - _0_23)))
end)) (fun uu____3477 -> (match (uu____3477) with
| (x, uu____3487) -> begin
(FStar_Unionfind.uvar_id x)
end))))


let new_universe_uvar_set : Prims.unit  ->  universe_uvar FStar_Util.set = (fun uu____3506 -> (FStar_Util.new_set (fun x y -> (let _0_26 = (FStar_Unionfind.uvar_id x)
in (let _0_25 = (FStar_Unionfind.uvar_id y)
in (_0_26 - _0_25)))) (fun x -> (FStar_Unionfind.uvar_id x))))


let new_universe_names_fifo_set : Prims.unit  ->  univ_name FStar_Util.fifo_set = (fun uu____3527 -> (FStar_Util.new_fifo_set (fun x y -> (FStar_String.compare (FStar_Ident.text_of_id x) (FStar_Ident.text_of_id y))) (fun x -> (FStar_Util.hashcode (FStar_Ident.text_of_id x)))))


let no_names : bv FStar_Util.set = (new_bv_set ())


let no_uvs : uvars = (new_uv_set ())


let no_universe_uvars : universe_uvar FStar_Util.set = (new_universe_uvar_set ())


let no_universe_names : univ_name FStar_Util.fifo_set = (new_universe_names_fifo_set ())


let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars; free_univ_names = no_universe_names}


let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))


let memo_no_names : bv FStar_Util.set Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))


let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))


let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))


let mk = (fun t topt r -> (let _0_28 = (FStar_Util.mk_ref topt)
in (let _0_27 = (FStar_Util.mk_ref None)
in {n = t; tk = _0_28; pos = r; vars = _0_27})))


let bv_to_tm : bv  ->  term = (fun bv -> (let _0_29 = (range_of_bv bv)
in ((mk (Tm_bvar (bv))) (Some (bv.sort.n)) _0_29)))


let bv_to_name : bv  ->  term = (fun bv -> (let _0_30 = (range_of_bv bv)
in ((mk (Tm_name (bv))) (Some (bv.sort.n)) _0_30)))


let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| uu____3632 -> begin
((mk (Tm_app (((t1), (args))))) k p)
end))


let mk_Tm_uinst : term  ->  universes  ->  term = (fun t uu___90_3648 -> (match (uu___90_3648) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (uu____3650) -> begin
((mk (Tm_uinst (((t), (us))))) None t.pos)
end
| uu____3659 -> begin
(failwith "Unexpected universe instantiation")
end)
end))


let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
((mk_Tm_app head (FStar_List.append args args')) kopt r)
end
| uu____3699 -> begin
((mk_Tm_app t args') kopt r)
end))


let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> ((extend_app_n t ((arg)::[])) kopt r))


let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  term = (fun lr pos -> ((mk (Tm_delayed ((let _0_31 = (FStar_Util.mk_ref None)
in ((lr), (_0_31)))))) None pos))


let mk_Total' : typ  ->  universe Prims.option  ->  comp = (fun t u -> ((mk (Total (((t), (u))))) None t.pos))


let mk_GTotal' : typ  ->  universe Prims.option  ->  comp = (fun t u -> ((mk (GTotal (((t), (u))))) None t.pos))


let mk_Total : typ  ->  comp = (fun t -> (mk_Total' t None))


let mk_GTotal : typ  ->  comp = (fun t -> (mk_GTotal' t None))


let mk_Comp : comp_typ  ->  comp = (fun ct -> ((mk (Comp (ct))) None ct.result_typ.pos))


let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun uu____3824 -> (match (uu____3824) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))


let mk_subst : subst_t  ->  subst_t = (fun s -> s)


let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_elt Prims.list = (fun x s -> (x)::s)


let argpos : arg  ->  FStar_Range.range = (fun x -> (Prims.fst x).pos)


let tun : (term', term') syntax = ((mk Tm_unknown) None FStar_Range.dummyRange)


let teff : (term', term') syntax = ((mk (Tm_constant (FStar_Const.Const_effect))) (Some (Tm_unknown)) FStar_Range.dummyRange)


let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| uu____3878 -> begin
false
end))


let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (uu____3882) -> begin
true
end
| uu____3883 -> begin
false
end))


let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident (("_"), (FStar_Range.dummyRange)))


let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = (Prims.parse_int "0"); sort = k})


let mk_binder : bv  ->  binder = (fun a -> ((a), (None)))


let null_binder : term  ->  binder = (fun t -> (let _0_32 = (null_bv t)
in ((_0_32), (None))))


let imp_tag : arg_qualifier = Implicit (false)


let iarg : term  ->  arg = (fun t -> ((t), (Some (imp_tag))))


let as_arg : term  ->  arg = (fun t -> ((t), (None)))


let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))


let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))


let is_top_level : letbinding Prims.list  ->  Prims.bool = (fun uu___91_3912 -> (match (uu___91_3912) with
| ({lbname = FStar_Util.Inr (uu____3914); lbunivs = uu____3915; lbtyp = uu____3916; lbeff = uu____3917; lbdef = uu____3918})::uu____3919 -> begin
true
end
| uu____3926 -> begin
false
end))


let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun uu____3934 out -> (match (uu____3934) with
| (x, uu____3941) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))


let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> ((t), (None))))))


let binders_of_freenames : freenames  ->  binders = (fun fvs -> (let _0_33 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _0_33 binders_of_list)))


let is_implicit : aqual  ->  Prims.bool = (fun uu___92_3963 -> (match (uu___92_3963) with
| Some (Implicit (uu____3964)) -> begin
true
end
| uu____3965 -> begin
false
end))


let as_implicit : Prims.bool  ->  aqual = (fun uu___93_3968 -> (match (uu___93_3968) with
| true -> begin
Some (imp_tag)
end
| uu____3969 -> begin
None
end))


let pat_bvs : pat  ->  bv Prims.list = (fun p -> (

let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (uu____3993, pats) -> begin
(FStar_List.fold_left (fun b uu____4011 -> (match (uu____4011) with
| (p, uu____4019) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj ((p)::uu____4025) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(failwith "impossible")
end))
in (let _0_34 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev _0_34))))


let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (

let x = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let gen = (fun uu____4050 -> ((FStar_Util.incr x);
(FStar_ST.read x);
))
in (

let reset = (fun uu____4060 -> (FStar_ST.write x (Prims.parse_int "0")))
in ((gen), (reset)))))


let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)


let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)


let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun uu___94_4082 -> (match (uu___94_4082) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))


let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (

let id = (FStar_Ident.mk_ident ((s), ((range_of_ropt r))))
in (let _0_35 = (next_id ())
in {ppname = id; index = _0_35; sort = t})))


let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv FStar_Ident.reserved_prefix ropt t))


let freshen_bv : bv  ->  bv = (fun bv -> (

let uu____4108 = (is_null_bv bv)
in (match (uu____4108) with
| true -> begin
(let _0_36 = Some ((range_of_bv bv))
in (new_bv _0_36 bv.sort))
end
| uu____4109 -> begin
(

let uu___97_4110 = bv
in (let _0_37 = (next_id ())
in {ppname = uu___97_4110.ppname; index = _0_37; sort = uu___97_4110.sort}))
end)))


let new_univ_name : FStar_Range.range Prims.option  ->  univ_name = (fun ropt -> (

let id = (next_id ())
in (FStar_Ident.mk_ident (let _0_39 = (let _0_38 = (FStar_Util.string_of_int id)
in (Prims.strcat "\'uu___" _0_38))
in ((_0_39), ((range_of_ropt ropt)))))))


let mkbv : FStar_Ident.ident  ->  Prims.int  ->  (term', term') syntax  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})


let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match (((l1), (l2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| uu____4160 -> begin
false
end))


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.fv_name.v fv2.fv_name.v))


let fv_eq_lid : fv  ->  FStar_Ident.lident  ->  Prims.bool = (fun fv lid -> (FStar_Ident.lid_equals fv.fv_name.v lid))


let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (

let uu___98_4197 = bv
in {ppname = (FStar_Ident.mk_ident ((bv.ppname.FStar_Ident.idText), (r))); index = uu___98_4197.index; sort = uu___98_4197.sort}))


let lid_as_fv : FStar_Ident.lident  ->  delta_depth  ->  fv_qual Prims.option  ->  fv = (fun l dd dq -> (let _0_40 = (withinfo l tun (FStar_Ident.range_of_lid l))
in {fv_name = _0_40; fv_delta = dd; fv_qual = dq}))


let fv_to_tm : fv  ->  term = (fun fv -> ((mk (Tm_fvar (fv))) None (FStar_Ident.range_of_lid fv.fv_name.v)))


let fvar : FStar_Ident.lident  ->  delta_depth  ->  fv_qual Prims.option  ->  term = (fun l dd dq -> (fv_to_tm (lid_as_fv l dd dq)))


let lid_of_fv : fv  ->  FStar_Ident.lid = (fun fv -> fv.fv_name.v)


let range_of_fv : fv  ->  FStar_Range.range = (fun fv -> (FStar_Ident.range_of_lid (lid_of_fv fv)))


let has_simple_attribute : term Prims.list  ->  Prims.string  ->  Prims.bool = (fun l s -> (FStar_List.existsb (fun uu___95_4257 -> (match (uu___95_4257) with
| {n = Tm_constant (FStar_Const.Const_string (data, uu____4261)); tk = uu____4262; pos = uu____4263; vars = uu____4264} when ((FStar_Util.string_of_unicode data) = s) -> begin
true
end
| uu____4269 -> begin
false
end)) l))




