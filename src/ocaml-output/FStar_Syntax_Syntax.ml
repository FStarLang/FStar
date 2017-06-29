
open Prims
open FStar_Pervasives
type 'a withinfo_t =
{v : 'a; p : FStar_Range.range}


let __proj__Mkwithinfo_t__item__v = (fun projectee -> (match (projectee) with
| {v = __fname__v; p = __fname__p} -> begin
__fname__v
end))


let __proj__Mkwithinfo_t__item__p = (fun projectee -> (match (projectee) with
| {v = __fname__v; p = __fname__p} -> begin
__fname__p
end))


type var =
FStar_Ident.lident withinfo_t


type sconst =
FStar_Const.sconst

type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string FStar_Pervasives_Native.option
| LightOff


let uu___is_SetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
true
end
| uu____53 -> begin
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
| uu____68 -> begin
false
end))


let __proj__ResetOptions__item___0 : pragma  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
_0
end))


let uu___is_LightOff : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LightOff -> begin
true
end
| uu____84 -> begin
false
end))


type 'a memo =
'a FStar_Pervasives_Native.option FStar_ST.ref

type version =
{major : Prims.int; minor : Prims.int}


let __proj__Mkversion__item__major : version  ->  Prims.int = (fun projectee -> (match (projectee) with
| {major = __fname__major; minor = __fname__minor} -> begin
__fname__major
end))


let __proj__Mkversion__item__minor : version  ->  Prims.int = (fun projectee -> (match (projectee) with
| {major = __fname__major; minor = __fname__minor} -> begin
__fname__minor
end))

type arg_qualifier =
| Implicit of Prims.bool
| Equality


let uu___is_Implicit : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_0) -> begin
true
end
| uu____119 -> begin
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
| uu____132 -> begin
false
end))


type aqual =
arg_qualifier FStar_Pervasives_Native.option

type universe =
| U_zero
| U_succ of universe
| U_max of universe Prims.list
| U_bvar of Prims.int
| U_name of FStar_Ident.ident
| U_unif of (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version)
| U_unknown


let uu___is_U_zero : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_zero -> begin
true
end
| uu____163 -> begin
false
end))


let uu___is_U_succ : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_succ (_0) -> begin
true
end
| uu____169 -> begin
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
| uu____184 -> begin
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
| uu____201 -> begin
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
| uu____215 -> begin
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
| uu____233 -> begin
false
end))


let __proj__U_unif__item___0 : universe  ->  (universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) = (fun projectee -> (match (projectee) with
| U_unif (_0) -> begin
_0
end))


let uu___is_U_unknown : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_unknown -> begin
true
end
| uu____258 -> begin
false
end))


type univ_name =
FStar_Ident.ident


type universe_uvar =
(universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version)


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
| uu____277 -> begin
false
end))


let uu___is_Delta_defined_at_level : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_defined_at_level (_0) -> begin
true
end
| uu____283 -> begin
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
| uu____296 -> begin
false
end))


let uu___is_Delta_abstract : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_abstract (_0) -> begin
true
end
| uu____302 -> begin
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
| Tm_abs of ((bv * aqual) Prims.list * (term', term') syntax * residual_comp FStar_Pervasives_Native.option)
| Tm_arrow of ((bv * aqual) Prims.list * (comp', Prims.unit) syntax)
| Tm_refine of (bv * (term', term') syntax)
| Tm_app of ((term', term') syntax * ((term', term') syntax * aqual) Prims.list)
| Tm_match of ((term', term') syntax * (pat' withinfo_t * (term', term') syntax FStar_Pervasives_Native.option * (term', term') syntax) Prims.list)
| Tm_ascribed of ((term', term') syntax * (((term', term') syntax, (comp', Prims.unit) syntax) FStar_Util.either * (term', term') syntax FStar_Pervasives_Native.option) * FStar_Ident.lident FStar_Pervasives_Native.option)
| Tm_let of ((Prims.bool * letbinding Prims.list) * (term', term') syntax)
| Tm_uvar of (((term', term') syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) * (term', term') syntax)
| Tm_delayed of (((term', term') syntax * (subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)) * (term', term') syntax memo)
| Tm_meta of ((term', term') syntax * metadata)
| Tm_unknown 
 and pat' =
| Pat_constant of sconst
| Pat_cons of (fv * (pat' withinfo_t * Prims.bool) Prims.list)
| Pat_var of bv
| Pat_wild of bv
| Pat_dot_term of (bv * (term', term') syntax) 
 and letbinding =
{lbname : (bv, fv) FStar_Util.either; lbunivs : univ_name Prims.list; lbtyp : (term', term') syntax; lbeff : FStar_Ident.lident; lbdef : (term', term') syntax} 
 and comp_typ =
{comp_univs : universes; effect_name : FStar_Ident.lident; result_typ : (term', term') syntax; effect_args : ((term', term') syntax * aqual) Prims.list; flags : cflags Prims.list} 
 and comp' =
| Total of ((term', term') syntax * universe FStar_Pervasives_Native.option)
| GTotal of ((term', term') syntax * universe FStar_Pervasives_Native.option)
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
| Meta_alien of (FStar_Dyn.dyn * Prims.string) 
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
{fv_name : var; fv_delta : delta_depth; fv_qual : fv_qual FStar_Pervasives_Native.option} 
 and free_vars =
{free_names : bv FStar_Util.set; free_uvars : (((term', term') syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) * (term', term') syntax) FStar_Util.set; free_univs : universe_uvar FStar_Util.set; free_univ_names : univ_name FStar_Util.fifo_set} 
 and lcomp =
{eff_name : FStar_Ident.lident; res_typ : (term', term') syntax; cflags : cflags Prims.list; comp : Prims.unit  ->  (comp', Prims.unit) syntax} 
 and residual_comp =
{residual_effect : FStar_Ident.lident; residual_typ : (term', term') syntax FStar_Pervasives_Native.option; residual_flags : cflags Prims.list}


let uu___is_Tm_bvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_bvar (_0) -> begin
true
end
| uu____810 -> begin
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
| uu____824 -> begin
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
| uu____838 -> begin
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
| uu____856 -> begin
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
| uu____882 -> begin
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
| uu____896 -> begin
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
| uu____919 -> begin
false
end))


let __proj__Tm_abs__item___0 : term'  ->  ((bv * aqual) Prims.list * (term', term') syntax * residual_comp FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_0) -> begin
_0
end))


let uu___is_Tm_arrow : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_arrow (_0) -> begin
true
end
| uu____967 -> begin
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
| uu____1006 -> begin
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
| uu____1041 -> begin
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
| uu____1096 -> begin
false
end))


let __proj__Tm_match__item___0 : term'  ->  ((term', term') syntax * (pat' withinfo_t * (term', term') syntax FStar_Pervasives_Native.option * (term', term') syntax) Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_0) -> begin
_0
end))


let uu___is_Tm_ascribed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_ascribed (_0) -> begin
true
end
| uu____1169 -> begin
false
end))


let __proj__Tm_ascribed__item___0 : term'  ->  ((term', term') syntax * (((term', term') syntax, (comp', Prims.unit) syntax) FStar_Util.either * (term', term') syntax FStar_Pervasives_Native.option) * FStar_Ident.lident FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_0) -> begin
_0
end))


let uu___is_Tm_let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_let (_0) -> begin
true
end
| uu____1241 -> begin
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
| uu____1286 -> begin
false
end))


let __proj__Tm_uvar__item___0 : term'  ->  (((term', term') syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Tm_uvar (_0) -> begin
_0
end))


let uu___is_Tm_delayed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_delayed (_0) -> begin
true
end
| uu____1344 -> begin
false
end))


let __proj__Tm_delayed__item___0 : term'  ->  (((term', term') syntax * (subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)) * (term', term') syntax memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_0) -> begin
_0
end))


let uu___is_Tm_meta : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_meta (_0) -> begin
true
end
| uu____1404 -> begin
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
| uu____1429 -> begin
false
end))


let uu___is_Pat_constant : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_constant (_0) -> begin
true
end
| uu____1435 -> begin
false
end))


let __proj__Pat_constant__item___0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_0) -> begin
_0
end))


let uu___is_Pat_cons : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_cons (_0) -> begin
true
end
| uu____1455 -> begin
false
end))


let __proj__Pat_cons__item___0 : pat'  ->  (fv * (pat' withinfo_t * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_0) -> begin
_0
end))


let uu___is_Pat_var : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_var (_0) -> begin
true
end
| uu____1487 -> begin
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
| uu____1501 -> begin
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
| uu____1519 -> begin
false
end))


let __proj__Pat_dot_term__item___0 : pat'  ->  (bv * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_0) -> begin
_0
end))


let __proj__Mkletbinding__item__lbname : letbinding  ->  (bv, fv) FStar_Util.either = (fun projectee -> (match (projectee) with
| {lbname = __fname__lbname; lbunivs = __fname__lbunivs; lbtyp = __fname__lbtyp; lbeff = __fname__lbeff; lbdef = __fname__lbdef} -> begin
__fname__lbname
end))


let __proj__Mkletbinding__item__lbunivs : letbinding  ->  univ_name Prims.list = (fun projectee -> (match (projectee) with
| {lbname = __fname__lbname; lbunivs = __fname__lbunivs; lbtyp = __fname__lbtyp; lbeff = __fname__lbeff; lbdef = __fname__lbdef} -> begin
__fname__lbunivs
end))


let __proj__Mkletbinding__item__lbtyp : letbinding  ->  (term', term') syntax = (fun projectee -> (match (projectee) with
| {lbname = __fname__lbname; lbunivs = __fname__lbunivs; lbtyp = __fname__lbtyp; lbeff = __fname__lbeff; lbdef = __fname__lbdef} -> begin
__fname__lbtyp
end))


let __proj__Mkletbinding__item__lbeff : letbinding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {lbname = __fname__lbname; lbunivs = __fname__lbunivs; lbtyp = __fname__lbtyp; lbeff = __fname__lbeff; lbdef = __fname__lbdef} -> begin
__fname__lbeff
end))


let __proj__Mkletbinding__item__lbdef : letbinding  ->  (term', term') syntax = (fun projectee -> (match (projectee) with
| {lbname = __fname__lbname; lbunivs = __fname__lbunivs; lbtyp = __fname__lbtyp; lbeff = __fname__lbeff; lbdef = __fname__lbdef} -> begin
__fname__lbdef
end))


let __proj__Mkcomp_typ__item__comp_univs : comp_typ  ->  universes = (fun projectee -> (match (projectee) with
| {comp_univs = __fname__comp_univs; effect_name = __fname__effect_name; result_typ = __fname__result_typ; effect_args = __fname__effect_args; flags = __fname__flags} -> begin
__fname__comp_univs
end))


let __proj__Mkcomp_typ__item__effect_name : comp_typ  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {comp_univs = __fname__comp_univs; effect_name = __fname__effect_name; result_typ = __fname__result_typ; effect_args = __fname__effect_args; flags = __fname__flags} -> begin
__fname__effect_name
end))


let __proj__Mkcomp_typ__item__result_typ : comp_typ  ->  (term', term') syntax = (fun projectee -> (match (projectee) with
| {comp_univs = __fname__comp_univs; effect_name = __fname__effect_name; result_typ = __fname__result_typ; effect_args = __fname__effect_args; flags = __fname__flags} -> begin
__fname__result_typ
end))


let __proj__Mkcomp_typ__item__effect_args : comp_typ  ->  ((term', term') syntax * aqual) Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = __fname__comp_univs; effect_name = __fname__effect_name; result_typ = __fname__result_typ; effect_args = __fname__effect_args; flags = __fname__flags} -> begin
__fname__effect_args
end))


let __proj__Mkcomp_typ__item__flags : comp_typ  ->  cflags Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = __fname__comp_univs; effect_name = __fname__effect_name; result_typ = __fname__result_typ; effect_args = __fname__effect_args; flags = __fname__flags} -> begin
__fname__flags
end))


let uu___is_Total : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Total (_0) -> begin
true
end
| uu____1745 -> begin
false
end))


let __proj__Total__item___0 : comp'  ->  ((term', term') syntax * universe FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Total (_0) -> begin
_0
end))


let uu___is_GTotal : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTotal (_0) -> begin
true
end
| uu____1779 -> begin
false
end))


let __proj__GTotal__item___0 : comp'  ->  ((term', term') syntax * universe FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| GTotal (_0) -> begin
_0
end))


let uu___is_Comp : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
true
end
| uu____1808 -> begin
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
| uu____1821 -> begin
false
end))


let uu___is_MLEFFECT : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLEFFECT -> begin
true
end
| uu____1826 -> begin
false
end))


let uu___is_RETURN : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RETURN -> begin
true
end
| uu____1831 -> begin
false
end))


let uu___is_PARTIAL_RETURN : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PARTIAL_RETURN -> begin
true
end
| uu____1836 -> begin
false
end))


let uu___is_SOMETRIVIAL : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SOMETRIVIAL -> begin
true
end
| uu____1841 -> begin
false
end))


let uu___is_LEMMA : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LEMMA -> begin
true
end
| uu____1846 -> begin
false
end))


let uu___is_CPS : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPS -> begin
true
end
| uu____1851 -> begin
false
end))


let uu___is_DECREASES : cflags  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
true
end
| uu____1859 -> begin
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
| uu____1885 -> begin
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
| uu____1917 -> begin
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
| uu____1934 -> begin
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
| uu____1957 -> begin
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
| uu____1975 -> begin
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
| uu____2006 -> begin
false
end))


let __proj__Meta_monadic_lift__item___0 : metadata  ->  (monad_name * monad_name * (term', term') syntax) = (fun projectee -> (match (projectee) with
| Meta_monadic_lift (_0) -> begin
_0
end))


let uu___is_Meta_alien : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_alien (_0) -> begin
true
end
| uu____2037 -> begin
false
end))


let __proj__Meta_alien__item___0 : metadata  ->  (FStar_Dyn.dyn * Prims.string) = (fun projectee -> (match (projectee) with
| Meta_alien (_0) -> begin
_0
end))


let uu___is_Data_app : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Data_app -> begin
true
end
| uu____2056 -> begin
false
end))


let uu___is_Sequence : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sequence -> begin
true
end
| uu____2061 -> begin
false
end))


let uu___is_Primop : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primop -> begin
true
end
| uu____2066 -> begin
false
end))


let uu___is_Masked_effect : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Masked_effect -> begin
true
end
| uu____2071 -> begin
false
end))


let uu___is_Meta_smt_pat : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_smt_pat -> begin
true
end
| uu____2076 -> begin
false
end))


let uu___is_Mutable_alloc : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable_alloc -> begin
true
end
| uu____2081 -> begin
false
end))


let uu___is_Mutable_rval : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable_rval -> begin
true
end
| uu____2086 -> begin
false
end))


let uu___is_Data_ctor : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Data_ctor -> begin
true
end
| uu____2091 -> begin
false
end))


let uu___is_Record_projector : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record_projector (_0) -> begin
true
end
| uu____2099 -> begin
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
| uu____2122 -> begin
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
| uu____2147 -> begin
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
| uu____2169 -> begin
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
| uu____2193 -> begin
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
| uu____2221 -> begin
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
| uu____2243 -> begin
false
end))


let __proj__UD__item___0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_0) -> begin
_0
end))


let __proj__Mksyntax__item__n = (fun projectee -> (match (projectee) with
| {n = __fname__n; tk = __fname__tk; pos = __fname__pos; vars = __fname__vars} -> begin
__fname__n
end))


let __proj__Mksyntax__item__tk = (fun projectee -> (match (projectee) with
| {n = __fname__n; tk = __fname__tk; pos = __fname__pos; vars = __fname__vars} -> begin
__fname__tk
end))


let __proj__Mksyntax__item__pos = (fun projectee -> (match (projectee) with
| {n = __fname__n; tk = __fname__tk; pos = __fname__pos; vars = __fname__vars} -> begin
__fname__pos
end))


let __proj__Mksyntax__item__vars = (fun projectee -> (match (projectee) with
| {n = __fname__n; tk = __fname__tk; pos = __fname__pos; vars = __fname__vars} -> begin
__fname__vars
end))


let __proj__Mkbv__item__ppname : bv  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {ppname = __fname__ppname; index = __fname__index; sort = __fname__sort} -> begin
__fname__ppname
end))


let __proj__Mkbv__item__index : bv  ->  Prims.int = (fun projectee -> (match (projectee) with
| {ppname = __fname__ppname; index = __fname__index; sort = __fname__sort} -> begin
__fname__index
end))


let __proj__Mkbv__item__sort : bv  ->  (term', term') syntax = (fun projectee -> (match (projectee) with
| {ppname = __fname__ppname; index = __fname__index; sort = __fname__sort} -> begin
__fname__sort
end))


let __proj__Mkfv__item__fv_name : fv  ->  var = (fun projectee -> (match (projectee) with
| {fv_name = __fname__fv_name; fv_delta = __fname__fv_delta; fv_qual = __fname__fv_qual} -> begin
__fname__fv_name
end))


let __proj__Mkfv__item__fv_delta : fv  ->  delta_depth = (fun projectee -> (match (projectee) with
| {fv_name = __fname__fv_name; fv_delta = __fname__fv_delta; fv_qual = __fname__fv_qual} -> begin
__fname__fv_delta
end))


let __proj__Mkfv__item__fv_qual : fv  ->  fv_qual FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fv_name = __fname__fv_name; fv_delta = __fname__fv_delta; fv_qual = __fname__fv_qual} -> begin
__fname__fv_qual
end))


let __proj__Mkfree_vars__item__free_names : free_vars  ->  bv FStar_Util.set = (fun projectee -> (match (projectee) with
| {free_names = __fname__free_names; free_uvars = __fname__free_uvars; free_univs = __fname__free_univs; free_univ_names = __fname__free_univ_names} -> begin
__fname__free_names
end))


let __proj__Mkfree_vars__item__free_uvars : free_vars  ->  (((term', term') syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) * (term', term') syntax) FStar_Util.set = (fun projectee -> (match (projectee) with
| {free_names = __fname__free_names; free_uvars = __fname__free_uvars; free_univs = __fname__free_univs; free_univ_names = __fname__free_univ_names} -> begin
__fname__free_uvars
end))


let __proj__Mkfree_vars__item__free_univs : free_vars  ->  universe_uvar FStar_Util.set = (fun projectee -> (match (projectee) with
| {free_names = __fname__free_names; free_uvars = __fname__free_uvars; free_univs = __fname__free_univs; free_univ_names = __fname__free_univ_names} -> begin
__fname__free_univs
end))


let __proj__Mkfree_vars__item__free_univ_names : free_vars  ->  univ_name FStar_Util.fifo_set = (fun projectee -> (match (projectee) with
| {free_names = __fname__free_names; free_uvars = __fname__free_uvars; free_univs = __fname__free_univs; free_univ_names = __fname__free_univ_names} -> begin
__fname__free_univ_names
end))


let __proj__Mklcomp__item__eff_name : lcomp  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {eff_name = __fname__eff_name; res_typ = __fname__res_typ; cflags = __fname__cflags; comp = __fname__comp} -> begin
__fname__eff_name
end))


let __proj__Mklcomp__item__res_typ : lcomp  ->  (term', term') syntax = (fun projectee -> (match (projectee) with
| {eff_name = __fname__eff_name; res_typ = __fname__res_typ; cflags = __fname__cflags; comp = __fname__comp} -> begin
__fname__res_typ
end))


let __proj__Mklcomp__item__cflags : lcomp  ->  cflags Prims.list = (fun projectee -> (match (projectee) with
| {eff_name = __fname__eff_name; res_typ = __fname__res_typ; cflags = __fname__cflags; comp = __fname__comp} -> begin
__fname__cflags
end))


let __proj__Mklcomp__item__comp : lcomp  ->  Prims.unit  ->  (comp', Prims.unit) syntax = (fun projectee -> (match (projectee) with
| {eff_name = __fname__eff_name; res_typ = __fname__res_typ; cflags = __fname__cflags; comp = __fname__comp} -> begin
__fname__comp
end))


let __proj__Mkresidual_comp__item__residual_effect : residual_comp  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {residual_effect = __fname__residual_effect; residual_typ = __fname__residual_typ; residual_flags = __fname__residual_flags} -> begin
__fname__residual_effect
end))


let __proj__Mkresidual_comp__item__residual_typ : residual_comp  ->  (term', term') syntax FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {residual_effect = __fname__residual_effect; residual_typ = __fname__residual_typ; residual_flags = __fname__residual_flags} -> begin
__fname__residual_typ
end))


let __proj__Mkresidual_comp__item__residual_flags : residual_comp  ->  cflags Prims.list = (fun projectee -> (match (projectee) with
| {residual_effect = __fname__residual_effect; residual_typ = __fname__residual_typ; residual_flags = __fname__residual_flags} -> begin
__fname__residual_flags
end))


type pat =
pat' withinfo_t


type term =
(term', term') syntax


type branch =
(pat' withinfo_t * (term', term') syntax FStar_Pervasives_Native.option * (term', term') syntax)


type comp =
(comp', Prims.unit) syntax


type ascription =
(((term', term') syntax, (comp', Prims.unit) syntax) FStar_Util.either * (term', term') syntax FStar_Pervasives_Native.option)


type typ =
(term', term') syntax


type arg =
((term', term') syntax * aqual)


type args =
((term', term') syntax * aqual) Prims.list


type binder =
(bv * aqual)


type binders =
(bv * aqual) Prims.list


type uvar =
((term', term') syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version)


type lbname =
(bv, fv) FStar_Util.either


type letbindings =
(Prims.bool * letbinding Prims.list)


type subst_ts =
(subst_elt Prims.list Prims.list * FStar_Range.range FStar_Pervasives_Native.option)


type freenames =
bv FStar_Util.set


type uvars =
(((term', term') syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) * (term', term') syntax) FStar_Util.set


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
| uu____2758 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____2763 -> begin
false
end))


let uu___is_Private : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____2768 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____2773 -> begin
false
end))


let uu___is_Visible_default : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible_default -> begin
true
end
| uu____2778 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____2783 -> begin
false
end))


let uu___is_Abstract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____2788 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____2793 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____2798 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____2803 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____2808 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____2813 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____2818 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____2823 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable (_0) -> begin
true
end
| uu____2829 -> begin
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
| uu____2843 -> begin
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
| uu____2859 -> begin
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
| uu____2883 -> begin
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
| uu____2913 -> begin
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
| uu____2939 -> begin
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
| uu____2952 -> begin
false
end))


let uu___is_HasMaskedEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HasMaskedEffect -> begin
true
end
| uu____2957 -> begin
false
end))


let uu___is_Effect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect -> begin
true
end
| uu____2962 -> begin
false
end))


let uu___is_OnlyName : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OnlyName -> begin
true
end
| uu____2967 -> begin
false
end))


type attribute =
term


type tycon =
(FStar_Ident.lident * binders * typ)

type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}


let __proj__Mkmonad_abbrev__item__mabbrev : monad_abbrev  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {mabbrev = __fname__mabbrev; parms = __fname__parms; def = __fname__def} -> begin
__fname__mabbrev
end))


let __proj__Mkmonad_abbrev__item__parms : monad_abbrev  ->  binders = (fun projectee -> (match (projectee) with
| {mabbrev = __fname__mabbrev; parms = __fname__parms; def = __fname__def} -> begin
__fname__parms
end))


let __proj__Mkmonad_abbrev__item__def : monad_abbrev  ->  typ = (fun projectee -> (match (projectee) with
| {mabbrev = __fname__mabbrev; parms = __fname__parms; def = __fname__def} -> begin
__fname__def
end))

type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift_wp : tscheme FStar_Pervasives_Native.option; lift : tscheme FStar_Pervasives_Native.option}


let __proj__Mksub_eff__item__source : sub_eff  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {source = __fname__source; target = __fname__target; lift_wp = __fname__lift_wp; lift = __fname__lift} -> begin
__fname__source
end))


let __proj__Mksub_eff__item__target : sub_eff  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {source = __fname__source; target = __fname__target; lift_wp = __fname__lift_wp; lift = __fname__lift} -> begin
__fname__target
end))


let __proj__Mksub_eff__item__lift_wp : sub_eff  ->  tscheme FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {source = __fname__source; target = __fname__target; lift_wp = __fname__lift_wp; lift = __fname__lift} -> begin
__fname__lift_wp
end))


let __proj__Mksub_eff__item__lift : sub_eff  ->  tscheme FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {source = __fname__source; target = __fname__target; lift_wp = __fname__lift_wp; lift = __fname__lift} -> begin
__fname__lift
end))

type action =
{action_name : FStar_Ident.lident; action_unqualified_name : FStar_Ident.ident; action_univs : univ_names; action_params : binders; action_defn : term; action_typ : typ}


let __proj__Mkaction__item__action_name : action  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {action_name = __fname__action_name; action_unqualified_name = __fname__action_unqualified_name; action_univs = __fname__action_univs; action_params = __fname__action_params; action_defn = __fname__action_defn; action_typ = __fname__action_typ} -> begin
__fname__action_name
end))


let __proj__Mkaction__item__action_unqualified_name : action  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {action_name = __fname__action_name; action_unqualified_name = __fname__action_unqualified_name; action_univs = __fname__action_univs; action_params = __fname__action_params; action_defn = __fname__action_defn; action_typ = __fname__action_typ} -> begin
__fname__action_unqualified_name
end))


let __proj__Mkaction__item__action_univs : action  ->  univ_names = (fun projectee -> (match (projectee) with
| {action_name = __fname__action_name; action_unqualified_name = __fname__action_unqualified_name; action_univs = __fname__action_univs; action_params = __fname__action_params; action_defn = __fname__action_defn; action_typ = __fname__action_typ} -> begin
__fname__action_univs
end))


let __proj__Mkaction__item__action_params : action  ->  binders = (fun projectee -> (match (projectee) with
| {action_name = __fname__action_name; action_unqualified_name = __fname__action_unqualified_name; action_univs = __fname__action_univs; action_params = __fname__action_params; action_defn = __fname__action_defn; action_typ = __fname__action_typ} -> begin
__fname__action_params
end))


let __proj__Mkaction__item__action_defn : action  ->  term = (fun projectee -> (match (projectee) with
| {action_name = __fname__action_name; action_unqualified_name = __fname__action_unqualified_name; action_univs = __fname__action_univs; action_params = __fname__action_params; action_defn = __fname__action_defn; action_typ = __fname__action_typ} -> begin
__fname__action_defn
end))


let __proj__Mkaction__item__action_typ : action  ->  typ = (fun projectee -> (match (projectee) with
| {action_name = __fname__action_name; action_unqualified_name = __fname__action_unqualified_name; action_univs = __fname__action_univs; action_params = __fname__action_params; action_defn = __fname__action_defn; action_typ = __fname__action_typ} -> begin
__fname__action_typ
end))

type eff_decl =
{cattributes : cflags Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret_wp : tscheme; bind_wp : tscheme; if_then_else : tscheme; ite_wp : tscheme; stronger : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme; repr : term; return_repr : tscheme; bind_repr : tscheme; actions : action Prims.list}


let __proj__Mkeff_decl__item__cattributes : eff_decl  ->  cflags Prims.list = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__cattributes
end))


let __proj__Mkeff_decl__item__mname : eff_decl  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__mname
end))


let __proj__Mkeff_decl__item__univs : eff_decl  ->  univ_names = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__univs
end))


let __proj__Mkeff_decl__item__binders : eff_decl  ->  binders = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__binders
end))


let __proj__Mkeff_decl__item__signature : eff_decl  ->  term = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__signature
end))


let __proj__Mkeff_decl__item__ret_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__ret_wp
end))


let __proj__Mkeff_decl__item__bind_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__bind_wp
end))


let __proj__Mkeff_decl__item__if_then_else : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__if_then_else
end))


let __proj__Mkeff_decl__item__ite_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__ite_wp
end))


let __proj__Mkeff_decl__item__stronger : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__stronger
end))


let __proj__Mkeff_decl__item__close_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__close_wp
end))


let __proj__Mkeff_decl__item__assert_p : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__assert_p
end))


let __proj__Mkeff_decl__item__assume_p : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__assume_p
end))


let __proj__Mkeff_decl__item__null_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__null_wp
end))


let __proj__Mkeff_decl__item__trivial : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__trivial
end))


let __proj__Mkeff_decl__item__repr : eff_decl  ->  term = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__repr
end))


let __proj__Mkeff_decl__item__return_repr : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__return_repr
end))


let __proj__Mkeff_decl__item__bind_repr : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__bind_repr
end))


let __proj__Mkeff_decl__item__actions : eff_decl  ->  action Prims.list = (fun projectee -> (match (projectee) with
| {cattributes = __fname__cattributes; mname = __fname__mname; univs = __fname__univs; binders = __fname__binders; signature = __fname__signature; ret_wp = __fname__ret_wp; bind_wp = __fname__bind_wp; if_then_else = __fname__if_then_else; ite_wp = __fname__ite_wp; stronger = __fname__stronger; close_wp = __fname__close_wp; assert_p = __fname__assert_p; assume_p = __fname__assume_p; null_wp = __fname__null_wp; trivial = __fname__trivial; repr = __fname__repr; return_repr = __fname__return_repr; bind_repr = __fname__bind_repr; actions = __fname__actions} -> begin
__fname__actions
end))

type sig_metadata =
{sigmeta_active : Prims.bool; sigmeta_fact_db_ids : Prims.string Prims.list}


let __proj__Mksig_metadata__item__sigmeta_active : sig_metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {sigmeta_active = __fname__sigmeta_active; sigmeta_fact_db_ids = __fname__sigmeta_fact_db_ids} -> begin
__fname__sigmeta_active
end))


let __proj__Mksig_metadata__item__sigmeta_fact_db_ids : sig_metadata  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {sigmeta_active = __fname__sigmeta_active; sigmeta_fact_db_ids = __fname__sigmeta_fact_db_ids} -> begin
__fname__sigmeta_fact_db_ids
end))

type sigelt' =
| Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list)
| Sig_bundle of (sigelt Prims.list * FStar_Ident.lident Prims.list)
| Sig_datacon of (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * FStar_Ident.lident Prims.list)
| Sig_declare_typ of (FStar_Ident.lident * univ_names * typ)
| Sig_let of (letbindings * FStar_Ident.lident Prims.list)
| Sig_main of term
| Sig_assume of (FStar_Ident.lident * univ_names * formula)
| Sig_new_effect of eff_decl
| Sig_new_effect_for_free of eff_decl
| Sig_sub_effect of sub_eff
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * cflags Prims.list)
| Sig_pragma of pragma 
 and sigelt =
{sigel : sigelt'; sigrng : FStar_Range.range; sigquals : qualifier Prims.list; sigmeta : sig_metadata; sigattrs : attribute Prims.list}


let uu___is_Sig_inductive_typ : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_0) -> begin
true
end
| uu____3849 -> begin
false
end))


let __proj__Sig_inductive_typ__item___0 : sigelt'  ->  (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list) = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_0) -> begin
_0
end))


let uu___is_Sig_bundle : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_bundle (_0) -> begin
true
end
| uu____3891 -> begin
false
end))


let __proj__Sig_bundle__item___0 : sigelt'  ->  (sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun projectee -> (match (projectee) with
| Sig_bundle (_0) -> begin
_0
end))


let uu___is_Sig_datacon : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_datacon (_0) -> begin
true
end
| uu____3924 -> begin
false
end))


let __proj__Sig_datacon__item___0 : sigelt'  ->  (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * FStar_Ident.lident Prims.list) = (fun projectee -> (match (projectee) with
| Sig_datacon (_0) -> begin
_0
end))


let uu___is_Sig_declare_typ : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_0) -> begin
true
end
| uu____3962 -> begin
false
end))


let __proj__Sig_declare_typ__item___0 : sigelt'  ->  (FStar_Ident.lident * univ_names * typ) = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_0) -> begin
_0
end))


let uu___is_Sig_let : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_let (_0) -> begin
true
end
| uu____3988 -> begin
false
end))


let __proj__Sig_let__item___0 : sigelt'  ->  (letbindings * FStar_Ident.lident Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_0) -> begin
_0
end))


let uu___is_Sig_main : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_main (_0) -> begin
true
end
| uu____4011 -> begin
false
end))


let __proj__Sig_main__item___0 : sigelt'  ->  term = (fun projectee -> (match (projectee) with
| Sig_main (_0) -> begin
_0
end))


let uu___is_Sig_assume : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_assume (_0) -> begin
true
end
| uu____4028 -> begin
false
end))


let __proj__Sig_assume__item___0 : sigelt'  ->  (FStar_Ident.lident * univ_names * formula) = (fun projectee -> (match (projectee) with
| Sig_assume (_0) -> begin
_0
end))


let uu___is_Sig_new_effect : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_new_effect (_0) -> begin
true
end
| uu____4051 -> begin
false
end))


let __proj__Sig_new_effect__item___0 : sigelt'  ->  eff_decl = (fun projectee -> (match (projectee) with
| Sig_new_effect (_0) -> begin
_0
end))


let uu___is_Sig_new_effect_for_free : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_new_effect_for_free (_0) -> begin
true
end
| uu____4065 -> begin
false
end))


let __proj__Sig_new_effect_for_free__item___0 : sigelt'  ->  eff_decl = (fun projectee -> (match (projectee) with
| Sig_new_effect_for_free (_0) -> begin
_0
end))


let uu___is_Sig_sub_effect : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_0) -> begin
true
end
| uu____4079 -> begin
false
end))


let __proj__Sig_sub_effect__item___0 : sigelt'  ->  sub_eff = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_0) -> begin
_0
end))


let uu___is_Sig_effect_abbrev : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_0) -> begin
true
end
| uu____4099 -> begin
false
end))


let __proj__Sig_effect_abbrev__item___0 : sigelt'  ->  (FStar_Ident.lident * univ_names * binders * comp * cflags Prims.list) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_0) -> begin
_0
end))


let uu___is_Sig_pragma : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_pragma (_0) -> begin
true
end
| uu____4131 -> begin
false
end))


let __proj__Sig_pragma__item___0 : sigelt'  ->  pragma = (fun projectee -> (match (projectee) with
| Sig_pragma (_0) -> begin
_0
end))


let __proj__Mksigelt__item__sigel : sigelt  ->  sigelt' = (fun projectee -> (match (projectee) with
| {sigel = __fname__sigel; sigrng = __fname__sigrng; sigquals = __fname__sigquals; sigmeta = __fname__sigmeta; sigattrs = __fname__sigattrs} -> begin
__fname__sigel
end))


let __proj__Mksigelt__item__sigrng : sigelt  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {sigel = __fname__sigel; sigrng = __fname__sigrng; sigquals = __fname__sigquals; sigmeta = __fname__sigmeta; sigattrs = __fname__sigattrs} -> begin
__fname__sigrng
end))


let __proj__Mksigelt__item__sigquals : sigelt  ->  qualifier Prims.list = (fun projectee -> (match (projectee) with
| {sigel = __fname__sigel; sigrng = __fname__sigrng; sigquals = __fname__sigquals; sigmeta = __fname__sigmeta; sigattrs = __fname__sigattrs} -> begin
__fname__sigquals
end))


let __proj__Mksigelt__item__sigmeta : sigelt  ->  sig_metadata = (fun projectee -> (match (projectee) with
| {sigel = __fname__sigel; sigrng = __fname__sigrng; sigquals = __fname__sigquals; sigmeta = __fname__sigmeta; sigattrs = __fname__sigattrs} -> begin
__fname__sigmeta
end))


let __proj__Mksigelt__item__sigattrs : sigelt  ->  attribute Prims.list = (fun projectee -> (match (projectee) with
| {sigel = __fname__sigel; sigrng = __fname__sigrng; sigquals = __fname__sigquals; sigmeta = __fname__sigmeta; sigattrs = __fname__sigattrs} -> begin
__fname__sigattrs
end))


type sigelts =
sigelt Prims.list

type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}


let __proj__Mkmodul__item__name : modul  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {name = __fname__name; declarations = __fname__declarations; exports = __fname__exports; is_interface = __fname__is_interface} -> begin
__fname__name
end))


let __proj__Mkmodul__item__declarations : modul  ->  sigelts = (fun projectee -> (match (projectee) with
| {name = __fname__name; declarations = __fname__declarations; exports = __fname__exports; is_interface = __fname__is_interface} -> begin
__fname__declarations
end))


let __proj__Mkmodul__item__exports : modul  ->  sigelts = (fun projectee -> (match (projectee) with
| {name = __fname__name; declarations = __fname__declarations; exports = __fname__exports; is_interface = __fname__is_interface} -> begin
__fname__exports
end))


let __proj__Mkmodul__item__is_interface : modul  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; declarations = __fname__declarations; exports = __fname__exports; is_interface = __fname__is_interface} -> begin
__fname__is_interface
end))


type path =
Prims.string Prims.list


type subst_t =
subst_elt Prims.list


type ('a, 'b) mk_t_a =
'b FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  ('a, 'b) syntax


type mk_t =
(term', term') mk_t_a


let contains_reflectable : qualifier Prims.list  ->  Prims.bool = (fun l -> (FStar_Util.for_some (fun uu___88_4273 -> (match (uu___88_4273) with
| Reflectable (uu____4274) -> begin
true
end
| uu____4275 -> begin
false
end)) l))


let withinfo = (fun v1 r -> {v = v1; p = r})


let withsort = (fun v1 -> (withinfo v1 FStar_Range.dummyRange))


let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))


let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (

let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(x.index - y.index)
end
| uu____4319 -> begin
i
end)))


let order_fv : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.int = (fun x y -> (FStar_String.compare x.FStar_Ident.str y.FStar_Ident.str))


let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.fv_name.v)
end))


let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)


let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (

let uu___95_4346 = x
in {ppname = (FStar_Ident.mk_ident ((x.ppname.FStar_Ident.idText), (r))); index = uu___95_4346.index; sort = uu___95_4346.sort}))


let syn = (fun p k f -> (f k p))


let mk_fvs = (fun uu____4395 -> (FStar_Util.mk_ref FStar_Pervasives_Native.None))


let mk_uvs = (fun uu____4409 -> (FStar_Util.mk_ref FStar_Pervasives_Native.None))


let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun uu____4416 -> (FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText)))))


let new_fv_set : Prims.unit  ->  FStar_Ident.lident FStar_Util.set = (fun uu____4424 -> (FStar_Util.new_set order_fv (fun x -> (FStar_Util.hashcode x.FStar_Ident.str))))


let new_universe_names_fifo_set : Prims.unit  ->  univ_name FStar_Util.fifo_set = (fun uu____4434 -> (FStar_Util.new_fifo_set (fun x y -> (FStar_String.compare (FStar_Ident.text_of_id x) (FStar_Ident.text_of_id y))) (fun x -> (FStar_Util.hashcode (FStar_Ident.text_of_id x)))))


let no_names : bv FStar_Util.set = (new_bv_set ())


let no_fvars : FStar_Ident.lident FStar_Util.set = (new_fv_set ())


let no_universe_names : univ_name FStar_Util.fifo_set = (new_universe_names_fifo_set ())


let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))


let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))


let mk = (fun t topt r -> (

let uu____4488 = (FStar_Util.mk_ref topt)
in (

let uu____4492 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {n = t; tk = uu____4488; pos = r; vars = uu____4492})))


let bv_to_tm : bv  ->  term = (fun bv -> (

let uu____4504 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (FStar_Pervasives_Native.Some (bv.sort.n)) uu____4504)))


let bv_to_name : bv  ->  term = (fun bv -> (

let uu____4513 = (range_of_bv bv)
in (mk (Tm_name (bv)) (FStar_Pervasives_Native.Some (bv.sort.n)) uu____4513)))


let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| uu____4536 -> begin
(mk (Tm_app (((t1), (args)))) k p)
end))


let mk_Tm_uinst : term  ->  universes  ->  term = (fun t uu___89_4550 -> (match (uu___89_4550) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (uu____4552) -> begin
(mk (Tm_uinst (((t), (us)))) FStar_Pervasives_Native.None t.pos)
end
| uu____4557 -> begin
(failwith "Unexpected universe instantiation")
end)
end))


let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head1, args) -> begin
(mk_Tm_app head1 (FStar_List.append args args') kopt r)
end
| uu____4597 -> begin
(mk_Tm_app t args' kopt r)
end))


let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))


let mk_Tm_delayed : (term * subst_ts)  ->  FStar_Range.range  ->  term = (fun lr pos -> (

let uu____4629 = (

let uu____4632 = (

let uu____4633 = (

let uu____4648 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((lr), (uu____4648)))
in Tm_delayed (uu____4633))
in (mk uu____4632))
in (uu____4629 FStar_Pervasives_Native.None pos)))


let mk_Total' : typ  ->  universe FStar_Pervasives_Native.option  ->  comp = (fun t u -> (mk (Total (((t), (u)))) FStar_Pervasives_Native.None t.pos))


let mk_GTotal' : typ  ->  universe FStar_Pervasives_Native.option  ->  comp = (fun t u -> (mk (GTotal (((t), (u)))) FStar_Pervasives_Native.None t.pos))


let mk_Total : typ  ->  comp = (fun t -> (mk_Total' t FStar_Pervasives_Native.None))


let mk_GTotal : typ  ->  comp = (fun t -> (mk_GTotal' t FStar_Pervasives_Native.None))


let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) FStar_Pervasives_Native.None ct.result_typ.pos))


let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun uu____4730 -> (match (uu____4730) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))


let default_sigmeta : sig_metadata = {sigmeta_active = true; sigmeta_fact_db_ids = []}


let mk_sigelt : sigelt'  ->  sigelt = (fun e -> {sigel = e; sigrng = FStar_Range.dummyRange; sigquals = []; sigmeta = default_sigmeta; sigattrs = []})


let mk_subst : subst_t  ->  subst_t = (fun s -> s)


let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_t = (fun x s -> (x)::s)


let argpos : arg  ->  FStar_Range.range = (fun x -> (FStar_Pervasives_Native.fst x).pos)


let tun : (term', term') syntax = (mk Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)


let teff : (term', term') syntax = (mk (Tm_constant (FStar_Const.Const_effect)) (FStar_Pervasives_Native.Some (Tm_unknown)) FStar_Range.dummyRange)


let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| uu____4784 -> begin
false
end))


let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (uu____4789) -> begin
true
end
| uu____4790 -> begin
false
end))


let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident (("_"), (FStar_Range.dummyRange)))


let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = (Prims.parse_int "0"); sort = k})


let mk_binder : bv  ->  binder = (fun a -> ((a), (FStar_Pervasives_Native.None)))


let null_binder : term  ->  binder = (fun t -> (

let uu____4804 = (null_bv t)
in ((uu____4804), (FStar_Pervasives_Native.None))))


let imp_tag : arg_qualifier = Implicit (false)


let iarg : term  ->  arg = (fun t -> ((t), (FStar_Pervasives_Native.Some (imp_tag))))


let as_arg : term  ->  arg = (fun t -> ((t), (FStar_Pervasives_Native.None)))


let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))


let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (FStar_Pervasives_Native.fst b)))


let is_top_level : letbinding Prims.list  ->  Prims.bool = (fun uu___90_4828 -> (match (uu___90_4828) with
| ({lbname = FStar_Util.Inr (uu____4830); lbunivs = uu____4831; lbtyp = uu____4832; lbeff = uu____4833; lbdef = uu____4834})::uu____4835 -> begin
true
end
| uu____4842 -> begin
false
end))


let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun uu____4855 out -> (match (uu____4855) with
| (x, uu____4862) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))


let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> ((t), (FStar_Pervasives_Native.None))))))


let binders_of_freenames : freenames  ->  binders = (fun fvs -> (

let uu____4884 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____4884 binders_of_list)))


let is_implicit : aqual  ->  Prims.bool = (fun uu___91_4890 -> (match (uu___91_4890) with
| FStar_Pervasives_Native.Some (Implicit (uu____4891)) -> begin
true
end
| uu____4892 -> begin
false
end))


let as_implicit : Prims.bool  ->  aqual = (fun uu___92_4896 -> (match (uu___92_4896) with
| true -> begin
FStar_Pervasives_Native.Some (imp_tag)
end
| uu____4897 -> begin
FStar_Pervasives_Native.None
end))


let pat_bvs : pat  ->  bv Prims.list = (fun p -> (

let rec aux = (fun b p1 -> (match (p1.v) with
| Pat_dot_term (uu____4917) -> begin
b
end
| Pat_constant (uu____4922) -> begin
b
end
| Pat_wild (x) -> begin
(x)::b
end
| Pat_var (x) -> begin
(x)::b
end
| Pat_cons (uu____4925, pats) -> begin
(FStar_List.fold_left (fun b1 uu____4944 -> (match (uu____4944) with
| (p2, uu____4951) -> begin
(aux b1 p2)
end)) b pats)
end))
in (

let uu____4954 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev uu____4954))))


let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (

let x = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let gen1 = (fun uu____4970 -> ((FStar_Util.incr x);
(FStar_ST.read x);
))
in (

let reset = (fun uu____4980 -> (FStar_ST.write x (Prims.parse_int "0")))
in ((gen1), (reset)))))


let next_id : Prims.unit  ->  Prims.int = (FStar_Pervasives_Native.fst gen_reset)


let reset_gensym : Prims.unit  ->  Prims.unit = (FStar_Pervasives_Native.snd gen_reset)


let range_of_ropt : FStar_Range.range FStar_Pervasives_Native.option  ->  FStar_Range.range = (fun uu___93_5005 -> (match (uu___93_5005) with
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end))


let gen_bv : Prims.string  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  typ  ->  bv = (fun s r t -> (

let id = (FStar_Ident.mk_ident ((s), ((range_of_ropt r))))
in (

let uu____5023 = (next_id ())
in {ppname = id; index = uu____5023; sort = t})))


let new_bv : FStar_Range.range FStar_Pervasives_Native.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv FStar_Ident.reserved_prefix ropt t))


let freshen_bv : bv  ->  bv = (fun bv -> (

let uu____5038 = (is_null_bv bv)
in (match (uu____5038) with
| true -> begin
(

let uu____5039 = (

let uu____5041 = (range_of_bv bv)
in FStar_Pervasives_Native.Some (uu____5041))
in (new_bv uu____5039 bv.sort))
end
| uu____5042 -> begin
(

let uu___96_5043 = bv
in (

let uu____5044 = (next_id ())
in {ppname = uu___96_5043.ppname; index = uu____5044; sort = uu___96_5043.sort}))
end)))


let new_univ_name : FStar_Range.range FStar_Pervasives_Native.option  ->  univ_name = (fun ropt -> (

let id = (next_id ())
in (

let uu____5052 = (

let uu____5055 = (

let uu____5056 = (FStar_Util.string_of_int id)
in (Prims.strcat FStar_Ident.reserved_prefix uu____5056))
in ((uu____5055), ((range_of_ropt ropt))))
in (FStar_Ident.mk_ident uu____5052))))


let mkbv : FStar_Ident.ident  ->  Prims.int  ->  (term', term') syntax  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})


let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match (((l1), (l2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| uu____5105 -> begin
false
end))


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.fv_name.v fv2.fv_name.v))


let fv_eq_lid : fv  ->  FStar_Ident.lident  ->  Prims.bool = (fun fv lid -> (FStar_Ident.lid_equals fv.fv_name.v lid))


let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (

let uu___97_5136 = bv
in {ppname = (FStar_Ident.mk_ident ((bv.ppname.FStar_Ident.idText), (r))); index = uu___97_5136.index; sort = uu___97_5136.sort}))


let lid_as_fv : FStar_Ident.lident  ->  delta_depth  ->  fv_qual FStar_Pervasives_Native.option  ->  fv = (fun l dd dq -> (

let uu____5151 = (withinfo l (FStar_Ident.range_of_lid l))
in {fv_name = uu____5151; fv_delta = dd; fv_qual = dq}))


let fv_to_tm : fv  ->  term = (fun fv -> (mk (Tm_fvar (fv)) FStar_Pervasives_Native.None (FStar_Ident.range_of_lid fv.fv_name.v)))


let fvar : FStar_Ident.lident  ->  delta_depth  ->  fv_qual FStar_Pervasives_Native.option  ->  term = (fun l dd dq -> (

let uu____5174 = (lid_as_fv l dd dq)
in (fv_to_tm uu____5174)))


let lid_of_fv : fv  ->  FStar_Ident.lid = (fun fv -> fv.fv_name.v)


let range_of_fv : fv  ->  FStar_Range.range = (fun fv -> (

let uu____5183 = (lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____5183)))


let set_range_of_fv : fv  ->  FStar_Range.range  ->  fv = (fun fv r -> (

let uu___98_5192 = fv
in (

let uu____5193 = (

let uu___99_5194 = fv.fv_name
in (

let uu____5195 = (

let uu____5196 = (lid_of_fv fv)
in (FStar_Ident.set_lid_range uu____5196 r))
in {v = uu____5195; p = uu___99_5194.p}))
in {fv_name = uu____5193; fv_delta = uu___98_5192.fv_delta; fv_qual = uu___98_5192.fv_qual})))


let has_simple_attribute : term Prims.list  ->  Prims.string  ->  Prims.bool = (fun l s -> (FStar_List.existsb (fun uu___94_5215 -> (match (uu___94_5215) with
| {n = Tm_constant (FStar_Const.Const_string (data, uu____5219)); tk = uu____5220; pos = uu____5221; vars = uu____5222} when ((FStar_Util.string_of_unicode data) = s) -> begin
true
end
| uu____5227 -> begin
false
end)) l))




