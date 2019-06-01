
open Prims
open FStar_Pervasives
type 'a withinfo_t =
{v : 'a; p : FStar_Range.range}


let __proj__Mkwithinfo_t__item__v : 'a . 'a withinfo_t  ->  'a = (fun projectee -> (match (projectee) with
| {v = v1; p = p} -> begin
v1
end))


let __proj__Mkwithinfo_t__item__p : 'a . 'a withinfo_t  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {v = v1; p = p} -> begin
p
end))


type var =
FStar_Ident.lident withinfo_t


type sconst =
FStar_Const.sconst

type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string FStar_Pervasives_Native.option
| PushOptions of Prims.string FStar_Pervasives_Native.option
| PopOptions
| LightOff


let uu___is_SetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
true
end
| uu____178 -> begin
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
| uu____203 -> begin
false
end))


let __proj__ResetOptions__item___0 : pragma  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
_0
end))


let uu___is_PushOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PushOptions (_0) -> begin
true
end
| uu____234 -> begin
false
end))


let __proj__PushOptions__item___0 : pragma  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| PushOptions (_0) -> begin
_0
end))


let uu___is_PopOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PopOptions -> begin
true
end
| uu____261 -> begin
false
end))


let uu___is_LightOff : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LightOff -> begin
true
end
| uu____272 -> begin
false
end))


type 'a memo =
'a FStar_Pervasives_Native.option FStar_ST.ref

type emb_typ =
| ET_abstract
| ET_fun of (emb_typ * emb_typ)
| ET_app of (Prims.string * emb_typ Prims.list)


let uu___is_ET_abstract : emb_typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ET_abstract -> begin
true
end
| uu____312 -> begin
false
end))


let uu___is_ET_fun : emb_typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ET_fun (_0) -> begin
true
end
| uu____328 -> begin
false
end))


let __proj__ET_fun__item___0 : emb_typ  ->  (emb_typ * emb_typ) = (fun projectee -> (match (projectee) with
| ET_fun (_0) -> begin
_0
end))


let uu___is_ET_app : emb_typ  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ET_app (_0) -> begin
true
end
| uu____366 -> begin
false
end))


let __proj__ET_app__item___0 : emb_typ  ->  (Prims.string * emb_typ Prims.list) = (fun projectee -> (match (projectee) with
| ET_app (_0) -> begin
_0
end))

type version =
{major : Prims.int; minor : Prims.int}


let __proj__Mkversion__item__major : version  ->  Prims.int = (fun projectee -> (match (projectee) with
| {major = major; minor = minor} -> begin
major
end))


let __proj__Mkversion__item__minor : version  ->  Prims.int = (fun projectee -> (match (projectee) with
| {major = major; minor = minor} -> begin
minor
end))

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
| uu____477 -> begin
false
end))


let uu___is_U_succ : universe  ->  Prims.bool = (fun projectee -> (match (projectee) with
| U_succ (_0) -> begin
true
end
| uu____489 -> begin
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
| uu____510 -> begin
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
| uu____536 -> begin
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
| uu____558 -> begin
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
| uu____585 -> begin
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
| uu____627 -> begin
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

type quote_kind =
| Quote_static
| Quote_dynamic


let uu___is_Quote_static : quote_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quote_static -> begin
true
end
| uu____650 -> begin
false
end))


let uu___is_Quote_dynamic : quote_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quote_dynamic -> begin
true
end
| uu____661 -> begin
false
end))

type maybe_set_use_range =
| NoUseRange
| SomeUseRange of FStar_Range.range


let uu___is_NoUseRange : maybe_set_use_range  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoUseRange -> begin
true
end
| uu____677 -> begin
false
end))


let uu___is_SomeUseRange : maybe_set_use_range  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SomeUseRange (_0) -> begin
true
end
| uu____689 -> begin
false
end))


let __proj__SomeUseRange__item___0 : maybe_set_use_range  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| SomeUseRange (_0) -> begin
_0
end))

type delta_depth =
| Delta_constant_at_level of Prims.int
| Delta_equational_at_level of Prims.int
| Delta_abstract of delta_depth


let uu___is_Delta_constant_at_level : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_constant_at_level (_0) -> begin
true
end
| uu____726 -> begin
false
end))


let __proj__Delta_constant_at_level__item___0 : delta_depth  ->  Prims.int = (fun projectee -> (match (projectee) with
| Delta_constant_at_level (_0) -> begin
_0
end))


let uu___is_Delta_equational_at_level : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_equational_at_level (_0) -> begin
true
end
| uu____749 -> begin
false
end))


let __proj__Delta_equational_at_level__item___0 : delta_depth  ->  Prims.int = (fun projectee -> (match (projectee) with
| Delta_equational_at_level (_0) -> begin
_0
end))


let uu___is_Delta_abstract : delta_depth  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta_abstract (_0) -> begin
true
end
| uu____771 -> begin
false
end))


let __proj__Delta_abstract__item___0 : delta_depth  ->  delta_depth = (fun projectee -> (match (projectee) with
| Delta_abstract (_0) -> begin
_0
end))

type should_check_uvar =
| Allow_unresolved
| Allow_untyped
| Strict


let uu___is_Allow_unresolved : should_check_uvar  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Allow_unresolved -> begin
true
end
| uu____789 -> begin
false
end))


let uu___is_Allow_untyped : should_check_uvar  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Allow_untyped -> begin
true
end
| uu____800 -> begin
false
end))


let uu___is_Strict : should_check_uvar  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Strict -> begin
true
end
| uu____811 -> begin
false
end))

type term' =
| Tm_bvar of bv
| Tm_name of bv
| Tm_fvar of fv
| Tm_uinst of (term' syntax * universes)
| Tm_constant of sconst
| Tm_type of universe
| Tm_abs of ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * term' syntax * residual_comp FStar_Pervasives_Native.option)
| Tm_arrow of ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * comp' syntax)
| Tm_refine of (bv * term' syntax)
| Tm_app of (term' syntax * (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list)
| Tm_match of (term' syntax * (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term' syntax) Prims.list)
| Tm_ascribed of (term' syntax * ((term' syntax, comp' syntax) FStar_Util.either * term' syntax FStar_Pervasives_Native.option) * FStar_Ident.lident FStar_Pervasives_Native.option)
| Tm_let of ((Prims.bool * letbinding Prims.list) * term' syntax)
| Tm_uvar of (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range))
| Tm_delayed of ((term' syntax * (subst_elt Prims.list Prims.list * maybe_set_use_range)) * term' syntax memo)
| Tm_meta of (term' syntax * metadata)
| Tm_lazy of lazyinfo
| Tm_quoted of (term' syntax * quoteinfo)
| Tm_unknown 
 and ctx_uvar =
{ctx_uvar_head : (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version); ctx_uvar_gamma : binding Prims.list; ctx_uvar_binders : (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list; ctx_uvar_typ : term' syntax; ctx_uvar_reason : Prims.string; ctx_uvar_should_check : should_check_uvar; ctx_uvar_range : FStar_Range.range; ctx_uvar_meta : (FStar_Dyn.dyn * term' syntax) FStar_Pervasives_Native.option} 
 and pat' =
| Pat_constant of sconst
| Pat_cons of (fv * (pat' withinfo_t * Prims.bool) Prims.list)
| Pat_var of bv
| Pat_wild of bv
| Pat_dot_term of (bv * term' syntax) 
 and letbinding =
{lbname : (bv, fv) FStar_Util.either; lbunivs : univ_name Prims.list; lbtyp : term' syntax; lbeff : FStar_Ident.lident; lbdef : term' syntax; lbattrs : term' syntax Prims.list; lbpos : FStar_Range.range} 
 and quoteinfo =
{qkind : quote_kind; antiquotes : (bv * term' syntax) Prims.list} 
 and comp_typ =
{comp_univs : universes; effect_name : FStar_Ident.lident; result_typ : term' syntax; effect_args : (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list; flags : cflag Prims.list} 
 and comp' =
| Total of (term' syntax * universe FStar_Pervasives_Native.option)
| GTotal of (term' syntax * universe FStar_Pervasives_Native.option)
| Comp of comp_typ 
 and cflag =
| TOTAL
| MLEFFECT
| LEMMA
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| TRIVIAL_POSTCONDITION
| SHOULD_NOT_INLINE
| CPS
| DECREASES of term' syntax 
 and metadata =
| Meta_pattern of (term' syntax Prims.list * (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list)
| Meta_named of FStar_Ident.lident
| Meta_labeled of (Prims.string * FStar_Range.range * Prims.bool)
| Meta_desugared of meta_source_info
| Meta_monadic of (monad_name * term' syntax)
| Meta_monadic_lift of (monad_name * monad_name * term' syntax) 
 and meta_source_info =
| Sequence
| Primop
| Masked_effect
| Meta_smt_pat 
 and fv_qual =
| Data_ctor
| Record_projector of (FStar_Ident.lident * FStar_Ident.ident)
| Record_ctor of (FStar_Ident.lident * FStar_Ident.ident Prims.list) 
 and subst_elt =
| DB of (Prims.int * bv)
| NM of (bv * Prims.int)
| NT of (bv * term' syntax)
| UN of (Prims.int * universe)
| UD of (univ_name * Prims.int) 
 and 'a syntax =
{n : 'a; pos : FStar_Range.range; vars : free_vars memo} 
 and bv =
{ppname : FStar_Ident.ident; index : Prims.int; sort : term' syntax} 
 and fv =
{fv_name : var; fv_delta : delta_depth; fv_qual : fv_qual FStar_Pervasives_Native.option} 
 and free_vars =
{free_names : bv Prims.list; free_uvars : ctx_uvar Prims.list; free_univs : universe_uvar Prims.list; free_univ_names : univ_name Prims.list} 
 and residual_comp =
{residual_effect : FStar_Ident.lident; residual_typ : term' syntax FStar_Pervasives_Native.option; residual_flags : cflag Prims.list} 
 and lazyinfo =
{blob : FStar_Dyn.dyn; lkind : lazy_kind; ltyp : term' syntax; rng : FStar_Range.range} 
 and lazy_kind =
| BadLazy
| Lazy_bv
| Lazy_binder
| Lazy_fvar
| Lazy_comp
| Lazy_env
| Lazy_proofstate
| Lazy_goal
| Lazy_sigelt
| Lazy_uvar
| Lazy_embedding of (emb_typ * term' syntax FStar_Common.thunk) 
 and binding =
| Binding_var of bv
| Binding_lid of (FStar_Ident.lident * (univ_name Prims.list * term' syntax))
| Binding_univ of univ_name 
 and arg_qualifier =
| Implicit of Prims.bool
| Meta of term' syntax
| Equality


let uu___is_Tm_bvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_bvar (_0) -> begin
true
end
| uu____1701 -> begin
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
| uu____1720 -> begin
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
| uu____1739 -> begin
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
| uu____1764 -> begin
false
end))


let __proj__Tm_uinst__item___0 : term'  ->  (term' syntax * universes) = (fun projectee -> (match (projectee) with
| Tm_uinst (_0) -> begin
_0
end))


let uu___is_Tm_constant : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_constant (_0) -> begin
true
end
| uu____1801 -> begin
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
| uu____1820 -> begin
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
| uu____1857 -> begin
false
end))


let __proj__Tm_abs__item___0 : term'  ->  ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * term' syntax * residual_comp FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_0) -> begin
_0
end))


let uu___is_Tm_arrow : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_arrow (_0) -> begin
true
end
| uu____1944 -> begin
false
end))


let __proj__Tm_arrow__item___0 : term'  ->  ((bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list * comp' syntax) = (fun projectee -> (match (projectee) with
| Tm_arrow (_0) -> begin
_0
end))


let uu___is_Tm_refine : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_refine (_0) -> begin
true
end
| uu____2011 -> begin
false
end))


let __proj__Tm_refine__item___0 : term'  ->  (bv * term' syntax) = (fun projectee -> (match (projectee) with
| Tm_refine (_0) -> begin
_0
end))


let uu___is_Tm_app : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_app (_0) -> begin
true
end
| uu____2064 -> begin
false
end))


let __proj__Tm_app__item___0 : term'  ->  (term' syntax * (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun projectee -> (match (projectee) with
| Tm_app (_0) -> begin
_0
end))


let uu___is_Tm_match : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_match (_0) -> begin
true
end
| uu____2153 -> begin
false
end))


let __proj__Tm_match__item___0 : term'  ->  (term' syntax * (pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term' syntax) Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_0) -> begin
_0
end))


let uu___is_Tm_ascribed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_ascribed (_0) -> begin
true
end
| uu____2264 -> begin
false
end))


let __proj__Tm_ascribed__item___0 : term'  ->  (term' syntax * ((term' syntax, comp' syntax) FStar_Util.either * term' syntax FStar_Pervasives_Native.option) * FStar_Ident.lident FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_0) -> begin
_0
end))


let uu___is_Tm_let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_let (_0) -> begin
true
end
| uu____2374 -> begin
false
end))


let __proj__Tm_let__item___0 : term'  ->  ((Prims.bool * letbinding Prims.list) * term' syntax) = (fun projectee -> (match (projectee) with
| Tm_let (_0) -> begin
_0
end))


let uu___is_Tm_uvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_uvar (_0) -> begin
true
end
| uu____2444 -> begin
false
end))


let __proj__Tm_uvar__item___0 : term'  ->  (ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range)) = (fun projectee -> (match (projectee) with
| Tm_uvar (_0) -> begin
_0
end))


let uu___is_Tm_delayed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_delayed (_0) -> begin
true
end
| uu____2521 -> begin
false
end))


let __proj__Tm_delayed__item___0 : term'  ->  ((term' syntax * (subst_elt Prims.list Prims.list * maybe_set_use_range)) * term' syntax memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_0) -> begin
_0
end))


let uu___is_Tm_meta : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_meta (_0) -> begin
true
end
| uu____2612 -> begin
false
end))


let __proj__Tm_meta__item___0 : term'  ->  (term' syntax * metadata) = (fun projectee -> (match (projectee) with
| Tm_meta (_0) -> begin
_0
end))


let uu___is_Tm_lazy : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_lazy (_0) -> begin
true
end
| uu____2649 -> begin
false
end))


let __proj__Tm_lazy__item___0 : term'  ->  lazyinfo = (fun projectee -> (match (projectee) with
| Tm_lazy (_0) -> begin
_0
end))


let uu___is_Tm_quoted : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_quoted (_0) -> begin
true
end
| uu____2674 -> begin
false
end))


let __proj__Tm_quoted__item___0 : term'  ->  (term' syntax * quoteinfo) = (fun projectee -> (match (projectee) with
| Tm_quoted (_0) -> begin
_0
end))


let uu___is_Tm_unknown : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tm_unknown -> begin
true
end
| uu____2710 -> begin
false
end))


let __proj__Mkctx_uvar__item__ctx_uvar_head : ctx_uvar  ->  (term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version) = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_head
end))


let __proj__Mkctx_uvar__item__ctx_uvar_gamma : ctx_uvar  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_gamma
end))


let __proj__Mkctx_uvar__item__ctx_uvar_binders : ctx_uvar  ->  (bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_binders
end))


let __proj__Mkctx_uvar__item__ctx_uvar_typ : ctx_uvar  ->  term' syntax = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_typ
end))


let __proj__Mkctx_uvar__item__ctx_uvar_reason : ctx_uvar  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_reason
end))


let __proj__Mkctx_uvar__item__ctx_uvar_should_check : ctx_uvar  ->  should_check_uvar = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_should_check
end))


let __proj__Mkctx_uvar__item__ctx_uvar_range : ctx_uvar  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_range
end))


let __proj__Mkctx_uvar__item__ctx_uvar_meta : ctx_uvar  ->  (FStar_Dyn.dyn * term' syntax) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {ctx_uvar_head = ctx_uvar_head; ctx_uvar_gamma = ctx_uvar_gamma; ctx_uvar_binders = ctx_uvar_binders; ctx_uvar_typ = ctx_uvar_typ; ctx_uvar_reason = ctx_uvar_reason; ctx_uvar_should_check = ctx_uvar_should_check; ctx_uvar_range = ctx_uvar_range; ctx_uvar_meta = ctx_uvar_meta} -> begin
ctx_uvar_meta
end))


let uu___is_Pat_constant : pat'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pat_constant (_0) -> begin
true
end
| uu____3144 -> begin
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
| uu____3176 -> begin
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
| uu____3234 -> begin
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
| uu____3253 -> begin
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
| uu____3278 -> begin
false
end))


let __proj__Pat_dot_term__item___0 : pat'  ->  (bv * term' syntax) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_0) -> begin
_0
end))


let __proj__Mkletbinding__item__lbname : letbinding  ->  (bv, fv) FStar_Util.either = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbname
end))


let __proj__Mkletbinding__item__lbunivs : letbinding  ->  univ_name Prims.list = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbunivs
end))


let __proj__Mkletbinding__item__lbtyp : letbinding  ->  term' syntax = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbtyp
end))


let __proj__Mkletbinding__item__lbeff : letbinding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbeff
end))


let __proj__Mkletbinding__item__lbdef : letbinding  ->  term' syntax = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbdef
end))


let __proj__Mkletbinding__item__lbattrs : letbinding  ->  term' syntax Prims.list = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbattrs
end))


let __proj__Mkletbinding__item__lbpos : letbinding  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {lbname = lbname; lbunivs = lbunivs; lbtyp = lbtyp; lbeff = lbeff; lbdef = lbdef; lbattrs = lbattrs; lbpos = lbpos} -> begin
lbpos
end))


let __proj__Mkquoteinfo__item__qkind : quoteinfo  ->  quote_kind = (fun projectee -> (match (projectee) with
| {qkind = qkind; antiquotes = antiquotes} -> begin
qkind
end))


let __proj__Mkquoteinfo__item__antiquotes : quoteinfo  ->  (bv * term' syntax) Prims.list = (fun projectee -> (match (projectee) with
| {qkind = qkind; antiquotes = antiquotes} -> begin
antiquotes
end))


let __proj__Mkcomp_typ__item__comp_univs : comp_typ  ->  universes = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
comp_univs
end))


let __proj__Mkcomp_typ__item__effect_name : comp_typ  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
effect_name
end))


let __proj__Mkcomp_typ__item__result_typ : comp_typ  ->  term' syntax = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
result_typ
end))


let __proj__Mkcomp_typ__item__effect_args : comp_typ  ->  (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
effect_args
end))


let __proj__Mkcomp_typ__item__flags : comp_typ  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
flags
end))


let uu___is_Total : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Total (_0) -> begin
true
end
| uu____3741 -> begin
false
end))


let __proj__Total__item___0 : comp'  ->  (term' syntax * universe FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Total (_0) -> begin
_0
end))


let uu___is_GTotal : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTotal (_0) -> begin
true
end
| uu____3792 -> begin
false
end))


let __proj__GTotal__item___0 : comp'  ->  (term' syntax * universe FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| GTotal (_0) -> begin
_0
end))


let uu___is_Comp : comp'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
true
end
| uu____3835 -> begin
false
end))


let __proj__Comp__item___0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
_0
end))


let uu___is_TOTAL : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TOTAL -> begin
true
end
| uu____3853 -> begin
false
end))


let uu___is_MLEFFECT : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLEFFECT -> begin
true
end
| uu____3864 -> begin
false
end))


let uu___is_LEMMA : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LEMMA -> begin
true
end
| uu____3875 -> begin
false
end))


let uu___is_RETURN : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RETURN -> begin
true
end
| uu____3886 -> begin
false
end))


let uu___is_PARTIAL_RETURN : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PARTIAL_RETURN -> begin
true
end
| uu____3897 -> begin
false
end))


let uu___is_SOMETRIVIAL : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SOMETRIVIAL -> begin
true
end
| uu____3908 -> begin
false
end))


let uu___is_TRIVIAL_POSTCONDITION : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TRIVIAL_POSTCONDITION -> begin
true
end
| uu____3919 -> begin
false
end))


let uu___is_SHOULD_NOT_INLINE : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SHOULD_NOT_INLINE -> begin
true
end
| uu____3930 -> begin
false
end))


let uu___is_CPS : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPS -> begin
true
end
| uu____3941 -> begin
false
end))


let uu___is_DECREASES : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
true
end
| uu____3955 -> begin
false
end))


let __proj__DECREASES__item___0 : cflag  ->  term' syntax = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
_0
end))


let uu___is_Meta_pattern : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_pattern (_0) -> begin
true
end
| uu____4000 -> begin
false
end))


let __proj__Meta_pattern__item___0 : metadata  ->  (term' syntax Prims.list * (term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list) = (fun projectee -> (match (projectee) with
| Meta_pattern (_0) -> begin
_0
end))


let uu___is_Meta_named : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_named (_0) -> begin
true
end
| uu____4079 -> begin
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
| uu____4106 -> begin
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
| uu____4149 -> begin
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
| uu____4174 -> begin
false
end))


let __proj__Meta_monadic__item___0 : metadata  ->  (monad_name * term' syntax) = (fun projectee -> (match (projectee) with
| Meta_monadic (_0) -> begin
_0
end))


let uu___is_Meta_monadic_lift : metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_monadic_lift (_0) -> begin
true
end
| uu____4219 -> begin
false
end))


let __proj__Meta_monadic_lift__item___0 : metadata  ->  (monad_name * monad_name * term' syntax) = (fun projectee -> (match (projectee) with
| Meta_monadic_lift (_0) -> begin
_0
end))


let uu___is_Sequence : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sequence -> begin
true
end
| uu____4261 -> begin
false
end))


let uu___is_Primop : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primop -> begin
true
end
| uu____4272 -> begin
false
end))


let uu___is_Masked_effect : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Masked_effect -> begin
true
end
| uu____4283 -> begin
false
end))


let uu___is_Meta_smt_pat : meta_source_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta_smt_pat -> begin
true
end
| uu____4294 -> begin
false
end))


let uu___is_Data_ctor : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Data_ctor -> begin
true
end
| uu____4305 -> begin
false
end))


let uu___is_Record_projector : fv_qual  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record_projector (_0) -> begin
true
end
| uu____4321 -> begin
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
| uu____4358 -> begin
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
| uu____4400 -> begin
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
| uu____4439 -> begin
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
| uu____4479 -> begin
false
end))


let __proj__NT__item___0 : subst_elt  ->  (bv * term' syntax) = (fun projectee -> (match (projectee) with
| NT (_0) -> begin
_0
end))


let uu___is_UN : subst_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UN (_0) -> begin
true
end
| uu____4521 -> begin
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
| uu____4560 -> begin
false
end))


let __proj__UD__item___0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_0) -> begin
_0
end))


let __proj__Mksyntax__item__n : 'a . 'a syntax  ->  'a = (fun projectee -> (match (projectee) with
| {n = n1; pos = pos; vars = vars} -> begin
n1
end))


let __proj__Mksyntax__item__pos : 'a . 'a syntax  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {n = n1; pos = pos; vars = vars} -> begin
pos
end))


let __proj__Mksyntax__item__vars : 'a . 'a syntax  ->  free_vars memo = (fun projectee -> (match (projectee) with
| {n = n1; pos = pos; vars = vars} -> begin
vars
end))


let __proj__Mkbv__item__ppname : bv  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {ppname = ppname; index = index1; sort = sort} -> begin
ppname
end))


let __proj__Mkbv__item__index : bv  ->  Prims.int = (fun projectee -> (match (projectee) with
| {ppname = ppname; index = index1; sort = sort} -> begin
index1
end))


let __proj__Mkbv__item__sort : bv  ->  term' syntax = (fun projectee -> (match (projectee) with
| {ppname = ppname; index = index1; sort = sort} -> begin
sort
end))


let __proj__Mkfv__item__fv_name : fv  ->  var = (fun projectee -> (match (projectee) with
| {fv_name = fv_name; fv_delta = fv_delta; fv_qual = fv_qual} -> begin
fv_name
end))


let __proj__Mkfv__item__fv_delta : fv  ->  delta_depth = (fun projectee -> (match (projectee) with
| {fv_name = fv_name; fv_delta = fv_delta; fv_qual = fv_qual} -> begin
fv_delta
end))


let __proj__Mkfv__item__fv_qual : fv  ->  fv_qual FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fv_name = fv_name; fv_delta = fv_delta; fv_qual = fv_qual} -> begin
fv_qual
end))


let __proj__Mkfree_vars__item__free_names : free_vars  ->  bv Prims.list = (fun projectee -> (match (projectee) with
| {free_names = free_names; free_uvars = free_uvars; free_univs = free_univs; free_univ_names = free_univ_names} -> begin
free_names
end))


let __proj__Mkfree_vars__item__free_uvars : free_vars  ->  ctx_uvar Prims.list = (fun projectee -> (match (projectee) with
| {free_names = free_names; free_uvars = free_uvars; free_univs = free_univs; free_univ_names = free_univ_names} -> begin
free_uvars
end))


let __proj__Mkfree_vars__item__free_univs : free_vars  ->  universe_uvar Prims.list = (fun projectee -> (match (projectee) with
| {free_names = free_names; free_uvars = free_uvars; free_univs = free_univs; free_univ_names = free_univ_names} -> begin
free_univs
end))


let __proj__Mkfree_vars__item__free_univ_names : free_vars  ->  univ_name Prims.list = (fun projectee -> (match (projectee) with
| {free_names = free_names; free_uvars = free_uvars; free_univs = free_univs; free_univ_names = free_univ_names} -> begin
free_univ_names
end))


let __proj__Mkresidual_comp__item__residual_effect : residual_comp  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {residual_effect = residual_effect; residual_typ = residual_typ; residual_flags = residual_flags} -> begin
residual_effect
end))


let __proj__Mkresidual_comp__item__residual_typ : residual_comp  ->  term' syntax FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {residual_effect = residual_effect; residual_typ = residual_typ; residual_flags = residual_flags} -> begin
residual_typ
end))


let __proj__Mkresidual_comp__item__residual_flags : residual_comp  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {residual_effect = residual_effect; residual_typ = residual_typ; residual_flags = residual_flags} -> begin
residual_flags
end))


let __proj__Mklazyinfo__item__blob : lazyinfo  ->  FStar_Dyn.dyn = (fun projectee -> (match (projectee) with
| {blob = blob; lkind = lkind; ltyp = ltyp; rng = rng} -> begin
blob
end))


let __proj__Mklazyinfo__item__lkind : lazyinfo  ->  lazy_kind = (fun projectee -> (match (projectee) with
| {blob = blob; lkind = lkind; ltyp = ltyp; rng = rng} -> begin
lkind
end))


let __proj__Mklazyinfo__item__ltyp : lazyinfo  ->  term' syntax = (fun projectee -> (match (projectee) with
| {blob = blob; lkind = lkind; ltyp = ltyp; rng = rng} -> begin
ltyp
end))


let __proj__Mklazyinfo__item__rng : lazyinfo  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {blob = blob; lkind = lkind; ltyp = ltyp; rng = rng} -> begin
rng
end))


let uu___is_BadLazy : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BadLazy -> begin
true
end
| uu____4931 -> begin
false
end))


let uu___is_Lazy_bv : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_bv -> begin
true
end
| uu____4942 -> begin
false
end))


let uu___is_Lazy_binder : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_binder -> begin
true
end
| uu____4953 -> begin
false
end))


let uu___is_Lazy_fvar : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_fvar -> begin
true
end
| uu____4964 -> begin
false
end))


let uu___is_Lazy_comp : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_comp -> begin
true
end
| uu____4975 -> begin
false
end))


let uu___is_Lazy_env : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_env -> begin
true
end
| uu____4986 -> begin
false
end))


let uu___is_Lazy_proofstate : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_proofstate -> begin
true
end
| uu____4997 -> begin
false
end))


let uu___is_Lazy_goal : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_goal -> begin
true
end
| uu____5008 -> begin
false
end))


let uu___is_Lazy_sigelt : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_sigelt -> begin
true
end
| uu____5019 -> begin
false
end))


let uu___is_Lazy_uvar : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_uvar -> begin
true
end
| uu____5030 -> begin
false
end))


let uu___is_Lazy_embedding : lazy_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy_embedding (_0) -> begin
true
end
| uu____5050 -> begin
false
end))


let __proj__Lazy_embedding__item___0 : lazy_kind  ->  (emb_typ * term' syntax FStar_Common.thunk) = (fun projectee -> (match (projectee) with
| Lazy_embedding (_0) -> begin
_0
end))


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____5093 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  bv = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_lid : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
true
end
| uu____5124 -> begin
false
end))


let __proj__Binding_lid__item___0 : binding  ->  (FStar_Ident.lident * (univ_name Prims.list * term' syntax)) = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
_0
end))


let uu___is_Binding_univ : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
true
end
| uu____5179 -> begin
false
end))


let __proj__Binding_univ__item___0 : binding  ->  univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
_0
end))


let uu___is_Implicit : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_0) -> begin
true
end
| uu____5199 -> begin
false
end))


let __proj__Implicit__item___0 : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_0) -> begin
_0
end))


let uu___is_Meta : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____5223 -> begin
false
end))


let __proj__Meta__item___0 : arg_qualifier  ->  term' syntax = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_Equality : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equality -> begin
true
end
| uu____5247 -> begin
false
end))


type subst_ts =
(subst_elt Prims.list Prims.list * maybe_set_use_range)


type ctx_uvar_and_subst =
(ctx_uvar * (subst_elt Prims.list Prims.list * maybe_set_use_range))


type term =
term' syntax


type uvar =
(term' syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * version)


type uvars =
ctx_uvar FStar_Util.set


type pat =
pat' withinfo_t


type branch =
(pat' withinfo_t * term' syntax FStar_Pervasives_Native.option * term' syntax)


type comp =
comp' syntax


type ascription =
((term' syntax, comp' syntax) FStar_Util.either * term' syntax FStar_Pervasives_Native.option)


type antiquotations =
(bv * term' syntax) Prims.list


type typ =
term' syntax


type aqual =
arg_qualifier FStar_Pervasives_Native.option


type arg =
(term' syntax * arg_qualifier FStar_Pervasives_Native.option)


type args =
(term' syntax * arg_qualifier FStar_Pervasives_Native.option) Prims.list


type binder =
(bv * arg_qualifier FStar_Pervasives_Native.option)


type binders =
(bv * arg_qualifier FStar_Pervasives_Native.option) Prims.list


type lbname =
(bv, fv) FStar_Util.either


type letbindings =
(Prims.bool * letbinding Prims.list)


type freenames =
bv FStar_Util.set


type attribute =
term' syntax


type tscheme =
(univ_name Prims.list * term' syntax)


type gamma =
binding Prims.list

type lcomp =
{eff_name : FStar_Ident.lident; res_typ : typ; cflags : cflag Prims.list; comp_thunk : (unit  ->  comp, comp) FStar_Util.either FStar_ST.ref}


let __proj__Mklcomp__item__eff_name : lcomp  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {eff_name = eff_name; res_typ = res_typ; cflags = cflags; comp_thunk = comp_thunk} -> begin
eff_name
end))


let __proj__Mklcomp__item__res_typ : lcomp  ->  typ = (fun projectee -> (match (projectee) with
| {eff_name = eff_name; res_typ = res_typ; cflags = cflags; comp_thunk = comp_thunk} -> begin
res_typ
end))


let __proj__Mklcomp__item__cflags : lcomp  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {eff_name = eff_name; res_typ = res_typ; cflags = cflags; comp_thunk = comp_thunk} -> begin
cflags
end))


let __proj__Mklcomp__item__comp_thunk : lcomp  ->  (unit  ->  comp, comp) FStar_Util.either FStar_ST.ref = (fun projectee -> (match (projectee) with
| {eff_name = eff_name; res_typ = res_typ; cflags = cflags; comp_thunk = comp_thunk} -> begin
comp_thunk
end))


let lazy_chooser : (lazy_kind  ->  lazyinfo  ->  term) FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let mk_lcomp : FStar_Ident.lident  ->  typ  ->  cflag Prims.list  ->  (unit  ->  comp)  ->  lcomp = (fun eff_name res_typ cflags comp_thunk -> (

let uu____5607 = (FStar_Util.mk_ref (FStar_Util.Inl (comp_thunk)))
in {eff_name = eff_name; res_typ = res_typ; cflags = cflags; comp_thunk = uu____5607}))


let lcomp_comp : lcomp  ->  comp = (fun lc -> (

let uu____5633 = (FStar_ST.op_Bang lc.comp_thunk)
in (match (uu____5633) with
| FStar_Util.Inl (thunk) -> begin
(

let c = (thunk ())
in ((FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr (c)));
c;
))
end
| FStar_Util.Inr (c) -> begin
c
end)))


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
| uu____5786 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____5797 -> begin
false
end))


let uu___is_Private : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____5808 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____5819 -> begin
false
end))


let uu___is_Visible_default : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible_default -> begin
true
end
| uu____5830 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____5841 -> begin
false
end))


let uu___is_Abstract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____5852 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____5863 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____5874 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____5885 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____5896 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____5907 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____5918 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____5929 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable (_0) -> begin
true
end
| uu____5941 -> begin
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
| uu____5960 -> begin
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
| uu____5983 -> begin
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
| uu____6022 -> begin
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
| uu____6073 -> begin
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
| uu____6116 -> begin
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
| uu____6134 -> begin
false
end))


let uu___is_HasMaskedEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HasMaskedEffect -> begin
true
end
| uu____6145 -> begin
false
end))


let uu___is_Effect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect -> begin
true
end
| uu____6156 -> begin
false
end))


let uu___is_OnlyName : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OnlyName -> begin
true
end
| uu____6167 -> begin
false
end))


type tycon =
(FStar_Ident.lident * binders * typ)

type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}


let __proj__Mkmonad_abbrev__item__mabbrev : monad_abbrev  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {mabbrev = mabbrev; parms = parms; def = def} -> begin
mabbrev
end))


let __proj__Mkmonad_abbrev__item__parms : monad_abbrev  ->  binders = (fun projectee -> (match (projectee) with
| {mabbrev = mabbrev; parms = parms; def = def} -> begin
parms
end))


let __proj__Mkmonad_abbrev__item__def : monad_abbrev  ->  typ = (fun projectee -> (match (projectee) with
| {mabbrev = mabbrev; parms = parms; def = def} -> begin
def
end))

type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift_wp : tscheme FStar_Pervasives_Native.option; lift : tscheme FStar_Pervasives_Native.option}


let __proj__Mksub_eff__item__source : sub_eff  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {source = source; target = target; lift_wp = lift_wp; lift = lift} -> begin
source
end))


let __proj__Mksub_eff__item__target : sub_eff  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {source = source; target = target; lift_wp = lift_wp; lift = lift} -> begin
target
end))


let __proj__Mksub_eff__item__lift_wp : sub_eff  ->  tscheme FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {source = source; target = target; lift_wp = lift_wp; lift = lift} -> begin
lift_wp
end))


let __proj__Mksub_eff__item__lift : sub_eff  ->  tscheme FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {source = source; target = target; lift_wp = lift_wp; lift = lift} -> begin
lift
end))

type action =
{action_name : FStar_Ident.lident; action_unqualified_name : FStar_Ident.ident; action_univs : univ_names; action_params : binders; action_defn : term; action_typ : typ}


let __proj__Mkaction__item__action_name : action  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {action_name = action_name; action_unqualified_name = action_unqualified_name; action_univs = action_univs; action_params = action_params; action_defn = action_defn; action_typ = action_typ} -> begin
action_name
end))


let __proj__Mkaction__item__action_unqualified_name : action  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {action_name = action_name; action_unqualified_name = action_unqualified_name; action_univs = action_univs; action_params = action_params; action_defn = action_defn; action_typ = action_typ} -> begin
action_unqualified_name
end))


let __proj__Mkaction__item__action_univs : action  ->  univ_names = (fun projectee -> (match (projectee) with
| {action_name = action_name; action_unqualified_name = action_unqualified_name; action_univs = action_univs; action_params = action_params; action_defn = action_defn; action_typ = action_typ} -> begin
action_univs
end))


let __proj__Mkaction__item__action_params : action  ->  binders = (fun projectee -> (match (projectee) with
| {action_name = action_name; action_unqualified_name = action_unqualified_name; action_univs = action_univs; action_params = action_params; action_defn = action_defn; action_typ = action_typ} -> begin
action_params
end))


let __proj__Mkaction__item__action_defn : action  ->  term = (fun projectee -> (match (projectee) with
| {action_name = action_name; action_unqualified_name = action_unqualified_name; action_univs = action_univs; action_params = action_params; action_defn = action_defn; action_typ = action_typ} -> begin
action_defn
end))


let __proj__Mkaction__item__action_typ : action  ->  typ = (fun projectee -> (match (projectee) with
| {action_name = action_name; action_unqualified_name = action_unqualified_name; action_univs = action_univs; action_params = action_params; action_defn = action_defn; action_typ = action_typ} -> begin
action_typ
end))

type eff_decl =
{cattributes : cflag Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret_wp : tscheme; bind_wp : tscheme; if_then_else : tscheme; ite_wp : tscheme; stronger : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme; repr : term; return_repr : tscheme; bind_repr : tscheme; actions : action Prims.list; eff_attrs : attribute Prims.list}


let __proj__Mkeff_decl__item__cattributes : eff_decl  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
cattributes
end))


let __proj__Mkeff_decl__item__mname : eff_decl  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
mname
end))


let __proj__Mkeff_decl__item__univs : eff_decl  ->  univ_names = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
univs
end))


let __proj__Mkeff_decl__item__binders : eff_decl  ->  binders = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
binders
end))


let __proj__Mkeff_decl__item__signature : eff_decl  ->  term = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
signature
end))


let __proj__Mkeff_decl__item__ret_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
ret_wp
end))


let __proj__Mkeff_decl__item__bind_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
bind_wp
end))


let __proj__Mkeff_decl__item__if_then_else : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
if_then_else
end))


let __proj__Mkeff_decl__item__ite_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
ite_wp
end))


let __proj__Mkeff_decl__item__stronger : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
stronger
end))


let __proj__Mkeff_decl__item__close_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
close_wp
end))


let __proj__Mkeff_decl__item__assert_p : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
assert_p
end))


let __proj__Mkeff_decl__item__assume_p : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
assume_p
end))


let __proj__Mkeff_decl__item__null_wp : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
null_wp
end))


let __proj__Mkeff_decl__item__trivial : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
trivial
end))


let __proj__Mkeff_decl__item__repr : eff_decl  ->  term = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
repr
end))


let __proj__Mkeff_decl__item__return_repr : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
return_repr
end))


let __proj__Mkeff_decl__item__bind_repr : eff_decl  ->  tscheme = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
bind_repr
end))


let __proj__Mkeff_decl__item__actions : eff_decl  ->  action Prims.list = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
actions
end))


let __proj__Mkeff_decl__item__eff_attrs : eff_decl  ->  attribute Prims.list = (fun projectee -> (match (projectee) with
| {cattributes = cattributes; mname = mname; univs = univs; binders = binders; signature = signature; ret_wp = ret_wp; bind_wp = bind_wp; if_then_else = if_then_else; ite_wp = ite_wp; stronger = stronger; close_wp = close_wp; assert_p = assert_p; assume_p = assume_p; null_wp = null_wp; trivial = trivial; repr = repr; return_repr = return_repr; bind_repr = bind_repr; actions = actions; eff_attrs = eff_attrs} -> begin
eff_attrs
end))

type sig_metadata =
{sigmeta_active : Prims.bool; sigmeta_fact_db_ids : Prims.string Prims.list}


let __proj__Mksig_metadata__item__sigmeta_active : sig_metadata  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {sigmeta_active = sigmeta_active; sigmeta_fact_db_ids = sigmeta_fact_db_ids} -> begin
sigmeta_active
end))


let __proj__Mksig_metadata__item__sigmeta_fact_db_ids : sig_metadata  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {sigmeta_active = sigmeta_active; sigmeta_fact_db_ids = sigmeta_fact_db_ids} -> begin
sigmeta_fact_db_ids
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
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * cflag Prims.list)
| Sig_pragma of pragma
| Sig_splice of (FStar_Ident.lident Prims.list * term) 
 and sigelt =
{sigel : sigelt'; sigrng : FStar_Range.range; sigquals : qualifier Prims.list; sigmeta : sig_metadata; sigattrs : attribute Prims.list}


let uu___is_Sig_inductive_typ : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_0) -> begin
true
end
| uu____7406 -> begin
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
| uu____7481 -> begin
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
| uu____7539 -> begin
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
| uu____7609 -> begin
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
| uu____7652 -> begin
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
| uu____7689 -> begin
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
| uu____7714 -> begin
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
| uu____7751 -> begin
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
| uu____7770 -> begin
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
| uu____7789 -> begin
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
| uu____7820 -> begin
false
end))


let __proj__Sig_effect_abbrev__item___0 : sigelt'  ->  (FStar_Ident.lident * univ_names * binders * comp * cflag Prims.list) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_0) -> begin
_0
end))


let uu___is_Sig_pragma : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_pragma (_0) -> begin
true
end
| uu____7875 -> begin
false
end))


let __proj__Sig_pragma__item___0 : sigelt'  ->  pragma = (fun projectee -> (match (projectee) with
| Sig_pragma (_0) -> begin
_0
end))


let uu___is_Sig_splice : sigelt'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sig_splice (_0) -> begin
true
end
| uu____7900 -> begin
false
end))


let __proj__Sig_splice__item___0 : sigelt'  ->  (FStar_Ident.lident Prims.list * term) = (fun projectee -> (match (projectee) with
| Sig_splice (_0) -> begin
_0
end))


let __proj__Mksigelt__item__sigel : sigelt  ->  sigelt' = (fun projectee -> (match (projectee) with
| {sigel = sigel; sigrng = sigrng; sigquals = sigquals; sigmeta = sigmeta; sigattrs = sigattrs} -> begin
sigel
end))


let __proj__Mksigelt__item__sigrng : sigelt  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {sigel = sigel; sigrng = sigrng; sigquals = sigquals; sigmeta = sigmeta; sigattrs = sigattrs} -> begin
sigrng
end))


let __proj__Mksigelt__item__sigquals : sigelt  ->  qualifier Prims.list = (fun projectee -> (match (projectee) with
| {sigel = sigel; sigrng = sigrng; sigquals = sigquals; sigmeta = sigmeta; sigattrs = sigattrs} -> begin
sigquals
end))


let __proj__Mksigelt__item__sigmeta : sigelt  ->  sig_metadata = (fun projectee -> (match (projectee) with
| {sigel = sigel; sigrng = sigrng; sigquals = sigquals; sigmeta = sigmeta; sigattrs = sigattrs} -> begin
sigmeta
end))


let __proj__Mksigelt__item__sigattrs : sigelt  ->  attribute Prims.list = (fun projectee -> (match (projectee) with
| {sigel = sigel; sigrng = sigrng; sigquals = sigquals; sigmeta = sigmeta; sigattrs = sigattrs} -> begin
sigattrs
end))


type sigelts =
sigelt Prims.list

type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}


let __proj__Mkmodul__item__name : modul  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {name = name; declarations = declarations; exports = exports; is_interface = is_interface} -> begin
name
end))


let __proj__Mkmodul__item__declarations : modul  ->  sigelts = (fun projectee -> (match (projectee) with
| {name = name; declarations = declarations; exports = exports; is_interface = is_interface} -> begin
declarations
end))


let __proj__Mkmodul__item__exports : modul  ->  sigelts = (fun projectee -> (match (projectee) with
| {name = name; declarations = declarations; exports = exports; is_interface = is_interface} -> begin
exports
end))


let __proj__Mkmodul__item__is_interface : modul  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = name; declarations = declarations; exports = exports; is_interface = is_interface} -> begin
is_interface
end))


let mod_name : modul  ->  FStar_Ident.lident = (fun m -> m.name)


type path =
Prims.string Prims.list


type subst_t =
subst_elt Prims.list


type 'a mk_t_a =
unit FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  'a syntax


type mk_t =
term' mk_t_a


let contains_reflectable : qualifier Prims.list  ->  Prims.bool = (fun l -> (FStar_Util.for_some (fun uu___0_8122 -> (match (uu___0_8122) with
| Reflectable (uu____8124) -> begin
true
end
| uu____8126 -> begin
false
end)) l))


let withinfo : 'a . 'a  ->  FStar_Range.range  ->  'a withinfo_t = (fun v1 r -> {v = v1; p = r})


let withsort : 'a . 'a  ->  'a withinfo_t = (fun v1 -> (withinfo v1 FStar_Range.dummyRange))


let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((Prims.op_Equality bv1.ppname.FStar_Ident.idText bv2.ppname.FStar_Ident.idText) && (Prims.op_Equality bv1.index bv2.index)))


let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (

let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(x.index - y.index)
end
| uu____8193 -> begin
i
end)))


let order_ident : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.int = (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))


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

let uu___422_8244 = x
in (

let uu____8245 = (FStar_Ident.mk_ident ((x.ppname.FStar_Ident.idText), (r)))
in {ppname = uu____8245; index = uu___422_8244.index; sort = uu___422_8244.sort})))


let on_antiquoted : (term  ->  term)  ->  quoteinfo  ->  quoteinfo = (fun f qi -> (

let aq = (FStar_List.map (fun uu____8282 -> (match (uu____8282) with
| (bv, t) -> begin
(

let uu____8293 = (f t)
in ((bv), (uu____8293)))
end)) qi.antiquotes)
in (

let uu___430_8294 = qi
in {qkind = uu___430_8294.qkind; antiquotes = aq})))


let lookup_aq : bv  ->  antiquotations  ->  term FStar_Pervasives_Native.option = (fun bv aq -> (

let uu____8310 = (FStar_List.tryFind (fun uu____8328 -> (match (uu____8328) with
| (bv', uu____8337) -> begin
(bv_eq bv bv')
end)) aq)
in (match (uu____8310) with
| FStar_Pervasives_Native.Some (uu____8344, e) -> begin
FStar_Pervasives_Native.Some (e)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let syn : 'Auu____8375 'Auu____8376 'Auu____8377 . 'Auu____8375  ->  'Auu____8376  ->  ('Auu____8376  ->  'Auu____8375  ->  'Auu____8377)  ->  'Auu____8377 = (fun p k f -> (f k p))


let mk_fvs : 'Auu____8408 . unit  ->  'Auu____8408 FStar_Pervasives_Native.option FStar_ST.ref = (fun uu____8417 -> (FStar_Util.mk_ref FStar_Pervasives_Native.None))


let mk_uvs : 'Auu____8425 . unit  ->  'Auu____8425 FStar_Pervasives_Native.option FStar_ST.ref = (fun uu____8434 -> (FStar_Util.mk_ref FStar_Pervasives_Native.None))


let new_bv_set : unit  ->  bv FStar_Util.set = (fun uu____8444 -> (FStar_Util.new_set order_bv))


let new_id_set : unit  ->  FStar_Ident.ident FStar_Util.set = (fun uu____8454 -> (FStar_Util.new_set order_ident))


let new_fv_set : unit  ->  FStar_Ident.lident FStar_Util.set = (fun uu____8464 -> (FStar_Util.new_set order_fv))


let order_univ_name : univ_name  ->  univ_name  ->  Prims.int = (fun x y -> (

let uu____8479 = (FStar_Ident.text_of_id x)
in (

let uu____8481 = (FStar_Ident.text_of_id y)
in (FStar_String.compare uu____8479 uu____8481))))


let new_universe_names_set : unit  ->  univ_name FStar_Util.set = (fun uu____8490 -> (FStar_Util.new_set order_univ_name))


let eq_binding : binding  ->  binding  ->  Prims.bool = (fun b1 b2 -> (match (((b1), (b2))) with
| (Binding_var (bv1), Binding_var (bv2)) -> begin
(bv_eq bv1 bv2)
end
| (Binding_lid (lid1, uu____8509), Binding_lid (lid2, uu____8511)) -> begin
(FStar_Ident.lid_equals lid1 lid2)
end
| (Binding_univ (u1), Binding_univ (u2)) -> begin
(FStar_Ident.ident_equals u1 u2)
end
| uu____8546 -> begin
false
end))


let no_names : freenames = (new_bv_set ())


let no_fvars : FStar_Ident.lident FStar_Util.set = (new_fv_set ())


let no_universe_names : univ_name FStar_Util.set = (new_universe_names_set ())


let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))


let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))


let mk : 'a . 'a  ->  'a mk_t_a = (fun t uu____8600 r -> (

let uu____8604 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {n = t; pos = r; vars = uu____8604}))


let bv_to_tm : bv  ->  term = (fun bv -> (

let uu____8615 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) FStar_Pervasives_Native.None uu____8615)))


let bv_to_name : bv  ->  term = (fun bv -> (

let uu____8622 = (range_of_bv bv)
in (mk (Tm_name (bv)) FStar_Pervasives_Native.None uu____8622)))


let binders_to_names : binders  ->  term Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____8652 -> (match (uu____8652) with
| (x, uu____8660) -> begin
(bv_to_name x)
end)))))


let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| uu____8690 -> begin
(mk (Tm_app (((t1), (args)))) FStar_Pervasives_Native.None p)
end))


let mk_Tm_uinst : term  ->  universes  ->  term = (fun t uu___1_8715 -> (match (uu___1_8715) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (uu____8717) -> begin
(mk (Tm_uinst (((t), (us)))) FStar_Pervasives_Native.None t.pos)
end
| uu____8720 -> begin
(failwith "Unexpected universe instantiation")
end)
end))


let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head1, args) -> begin
(mk_Tm_app head1 (FStar_List.append args args') kopt r)
end
| uu____8779 -> begin
(mk_Tm_app t args' kopt r)
end))


let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))


let mk_Tm_delayed : (term * subst_ts)  ->  FStar_Range.range  ->  term = (fun lr pos -> (

let uu____8836 = (

let uu____8843 = (

let uu____8844 = (

let uu____8867 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((lr), (uu____8867)))
in Tm_delayed (uu____8844))
in (mk uu____8843))
in (uu____8836 FStar_Pervasives_Native.None pos)))


let mk_Total' : typ  ->  universe FStar_Pervasives_Native.option  ->  comp = (fun t u -> (mk (Total (((t), (u)))) FStar_Pervasives_Native.None t.pos))


let mk_GTotal' : typ  ->  universe FStar_Pervasives_Native.option  ->  comp = (fun t u -> (mk (GTotal (((t), (u)))) FStar_Pervasives_Native.None t.pos))


let mk_Total : typ  ->  comp = (fun t -> (mk_Total' t FStar_Pervasives_Native.None))


let mk_GTotal : typ  ->  comp = (fun t -> (mk_GTotal' t FStar_Pervasives_Native.None))


let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) FStar_Pervasives_Native.None ct.result_typ.pos))


let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term * attribute Prims.list * FStar_Range.range)  ->  letbinding = (fun uu____8975 -> (match (uu____8975) with
| (x, univs, eff, t, e, attrs, pos) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e; lbattrs = attrs; lbpos = pos}
end))


let default_sigmeta : sig_metadata = {sigmeta_active = true; sigmeta_fact_db_ids = []}


let mk_sigelt : sigelt'  ->  sigelt = (fun e -> {sigel = e; sigrng = FStar_Range.dummyRange; sigquals = []; sigmeta = default_sigmeta; sigattrs = []})


let mk_subst : subst_t  ->  subst_t = (fun s -> s)


let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_t = (fun x s -> (x)::s)


let argpos : arg  ->  FStar_Range.range = (fun x -> (FStar_Pervasives_Native.fst x).pos)


let tun : term = (mk Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)


let teff : term = (mk (Tm_constant (FStar_Const.Const_effect)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| uu____9060 -> begin
false
end))


let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (uu____9070) -> begin
true
end
| uu____9072 -> begin
false
end))


let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident (("_"), (FStar_Range.dummyRange)))


let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = (Prims.parse_int "0"); sort = k})


let mk_binder : bv  ->  binder = (fun a -> ((a), (FStar_Pervasives_Native.None)))


let null_binder : term  ->  binder = (fun t -> (

let uu____9098 = (null_bv t)
in ((uu____9098), (FStar_Pervasives_Native.None))))


let imp_tag : arg_qualifier = Implicit (false)


let iarg : term  ->  arg = (fun t -> ((t), (FStar_Pervasives_Native.Some (imp_tag))))


let as_arg : term  ->  arg = (fun t -> ((t), (FStar_Pervasives_Native.None)))


let is_null_bv : bv  ->  Prims.bool = (fun b -> (Prims.op_Equality b.ppname.FStar_Ident.idText null_id.FStar_Ident.idText))


let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (FStar_Pervasives_Native.fst b)))


let is_top_level : letbinding Prims.list  ->  Prims.bool = (fun uu___2_9148 -> (match (uu___2_9148) with
| ({lbname = FStar_Util.Inr (uu____9152); lbunivs = uu____9153; lbtyp = uu____9154; lbeff = uu____9155; lbdef = uu____9156; lbattrs = uu____9157; lbpos = uu____9158})::uu____9159 -> begin
true
end
| uu____9173 -> begin
false
end))


let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun uu____9195 out -> (match (uu____9195) with
| (x, uu____9208) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))


let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> ((t), (FStar_Pervasives_Native.None))))))


let binders_of_freenames : freenames  ->  binders = (fun fvs -> (

let uu____9241 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____9241 binders_of_list)))


let is_implicit : aqual  ->  Prims.bool = (fun uu___3_9252 -> (match (uu___3_9252) with
| FStar_Pervasives_Native.Some (Implicit (uu____9254)) -> begin
true
end
| uu____9257 -> begin
false
end))


let as_implicit : Prims.bool  ->  aqual = (fun uu___4_9265 -> (match (uu___4_9265) with
| true -> begin
FStar_Pervasives_Native.Some (imp_tag)
end
| uu____9268 -> begin
FStar_Pervasives_Native.None
end))


let pat_bvs : pat  ->  bv Prims.list = (fun p -> (

let rec aux = (fun b p1 -> (match (p1.v) with
| Pat_dot_term (uu____9303) -> begin
b
end
| Pat_constant (uu____9310) -> begin
b
end
| Pat_wild (x) -> begin
(x)::b
end
| Pat_var (x) -> begin
(x)::b
end
| Pat_cons (uu____9313, pats) -> begin
(FStar_List.fold_left (fun b1 uu____9347 -> (match (uu____9347) with
| (p2, uu____9360) -> begin
(aux b1 p2)
end)) b pats)
end))
in (

let uu____9367 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev uu____9367))))


let range_of_ropt : FStar_Range.range FStar_Pervasives_Native.option  ->  FStar_Range.range = (fun uu___5_9381 -> (match (uu___5_9381) with
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end))


let gen_bv : Prims.string  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  typ  ->  bv = (fun s r t -> (

let id1 = (FStar_Ident.mk_ident ((s), ((range_of_ropt r))))
in (

let uu____9421 = (FStar_Ident.next_id ())
in {ppname = id1; index = uu____9421; sort = t})))


let new_bv : FStar_Range.range FStar_Pervasives_Native.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv FStar_Ident.reserved_prefix ropt t))


let freshen_bv : bv  ->  bv = (fun bv -> (

let uu____9444 = (is_null_bv bv)
in (match (uu____9444) with
| true -> begin
(

let uu____9447 = (

let uu____9450 = (range_of_bv bv)
in FStar_Pervasives_Native.Some (uu____9450))
in (new_bv uu____9447 bv.sort))
end
| uu____9451 -> begin
(

let uu___611_9453 = bv
in (

let uu____9454 = (FStar_Ident.next_id ())
in {ppname = uu___611_9453.ppname; index = uu____9454; sort = uu___611_9453.sort}))
end)))


let freshen_binder : binder  ->  binder = (fun b -> (

let uu____9462 = b
in (match (uu____9462) with
| (bv, aq) -> begin
(

let uu____9469 = (freshen_bv bv)
in ((uu____9469), (aq)))
end)))


let new_univ_name : FStar_Range.range FStar_Pervasives_Native.option  ->  univ_name = (fun ropt -> (

let id1 = (FStar_Ident.next_id ())
in (

let uu____9484 = (

let uu____9490 = (

let uu____9492 = (FStar_Util.string_of_int id1)
in (Prims.op_Hat FStar_Ident.reserved_prefix uu____9492))
in ((uu____9490), ((range_of_ropt ropt))))
in (FStar_Ident.mk_ident uu____9484))))


let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term' syntax  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})


let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match (((l1), (l2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| uu____9574 -> begin
false
end))


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.fv_name.v fv2.fv_name.v))


let fv_eq_lid : fv  ->  FStar_Ident.lident  ->  Prims.bool = (fun fv lid -> (FStar_Ident.lid_equals fv.fv_name.v lid))


let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (

let uu___641_9623 = bv
in (

let uu____9624 = (FStar_Ident.mk_ident ((bv.ppname.FStar_Ident.idText), (r)))
in {ppname = uu____9624; index = uu___641_9623.index; sort = uu___641_9623.sort})))


let lid_as_fv : FStar_Ident.lident  ->  delta_depth  ->  fv_qual FStar_Pervasives_Native.option  ->  fv = (fun l dd dq -> (

let uu____9646 = (

let uu____9647 = (FStar_Ident.range_of_lid l)
in (withinfo l uu____9647))
in {fv_name = uu____9646; fv_delta = dd; fv_qual = dq}))


let fv_to_tm : fv  ->  term = (fun fv -> (

let uu____9654 = (FStar_Ident.range_of_lid fv.fv_name.v)
in (mk (Tm_fvar (fv)) FStar_Pervasives_Native.None uu____9654)))


let fvar : FStar_Ident.lident  ->  delta_depth  ->  fv_qual FStar_Pervasives_Native.option  ->  term = (fun l dd dq -> (

let uu____9675 = (lid_as_fv l dd dq)
in (fv_to_tm uu____9675)))


let lid_of_fv : fv  ->  FStar_Ident.lid = (fun fv -> fv.fv_name.v)


let range_of_fv : fv  ->  FStar_Range.range = (fun fv -> (

let uu____9688 = (lid_of_fv fv)
in (FStar_Ident.range_of_lid uu____9688)))


let set_range_of_fv : fv  ->  FStar_Range.range  ->  fv = (fun fv r -> (

let uu___654_9700 = fv
in (

let uu____9701 = (

let uu___656_9702 = fv.fv_name
in (

let uu____9703 = (

let uu____9704 = (lid_of_fv fv)
in (FStar_Ident.set_lid_range uu____9704 r))
in {v = uu____9703; p = uu___656_9702.p}))
in {fv_name = uu____9701; fv_delta = uu___654_9700.fv_delta; fv_qual = uu___654_9700.fv_qual})))


let has_simple_attribute : term Prims.list  ->  Prims.string  ->  Prims.bool = (fun l s -> (FStar_List.existsb (fun uu___6_9730 -> (match (uu___6_9730) with
| {n = Tm_constant (FStar_Const.Const_string (data, uu____9735)); pos = uu____9736; vars = uu____9737} when (Prims.op_Equality data s) -> begin
true
end
| uu____9744 -> begin
false
end)) l))


let rec eq_pat : pat  ->  pat  ->  Prims.bool = (fun p1 p2 -> (match (((p1.v), (p2.v))) with
| (Pat_constant (c1), Pat_constant (c2)) -> begin
(FStar_Const.eq_const c1 c2)
end
| (Pat_cons (fv1, as1), Pat_cons (fv2, as2)) -> begin
(

let uu____9803 = (fv_eq fv1 fv2)
in (match (uu____9803) with
| true -> begin
(

let uu____9808 = (FStar_List.zip as1 as2)
in (FStar_All.pipe_right uu____9808 (FStar_List.for_all (fun uu____9875 -> (match (uu____9875) with
| ((p11, b1), (p21, b2)) -> begin
((Prims.op_Equality b1 b2) && (eq_pat p11 p21))
end)))))
end
| uu____9910 -> begin
false
end))
end
| (Pat_var (uu____9913), Pat_var (uu____9914)) -> begin
true
end
| (Pat_wild (uu____9916), Pat_wild (uu____9917)) -> begin
true
end
| (Pat_dot_term (bv1, t1), Pat_dot_term (bv2, t2)) -> begin
true
end
| (uu____9932, uu____9933) -> begin
false
end))


let delta_constant : delta_depth = Delta_constant_at_level ((Prims.parse_int "0"))


let delta_equational : delta_depth = Delta_equational_at_level ((Prims.parse_int "0"))


let fvconst : FStar_Ident.lident  ->  fv = (fun l -> (lid_as_fv l delta_constant FStar_Pervasives_Native.None))


let tconst : FStar_Ident.lident  ->  term = (fun l -> (

let uu____9951 = (

let uu____9958 = (

let uu____9959 = (fvconst l)
in Tm_fvar (uu____9959))
in (mk uu____9958))
in (uu____9951 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let tabbrev : FStar_Ident.lident  ->  term = (fun l -> (

let uu____9966 = (

let uu____9973 = (

let uu____9974 = (lid_as_fv l (Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in Tm_fvar (uu____9974))
in (mk uu____9973))
in (uu____9966 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let tdataconstr : FStar_Ident.lident  ->  term = (fun l -> (

let uu____9982 = (lid_as_fv l delta_constant (FStar_Pervasives_Native.Some (Data_ctor)))
in (fv_to_tm uu____9982)))


let t_unit : term = (tconst FStar_Parser_Const.unit_lid)


let t_bool : term = (tconst FStar_Parser_Const.bool_lid)


let t_int : term = (tconst FStar_Parser_Const.int_lid)


let t_string : term = (tconst FStar_Parser_Const.string_lid)


let t_exn : term = (tconst FStar_Parser_Const.exn_lid)


let t_real : term = (tconst FStar_Parser_Const.real_lid)


let t_float : term = (tconst FStar_Parser_Const.float_lid)


let t_char : term = (tabbrev FStar_Parser_Const.char_lid)


let t_range : term = (tconst FStar_Parser_Const.range_lid)


let t_term : term = (tconst FStar_Parser_Const.term_lid)


let t_order : term = (tconst FStar_Parser_Const.order_lid)


let t_decls : term = (tabbrev FStar_Parser_Const.decls_lid)


let t_binder : term = (tconst FStar_Parser_Const.binder_lid)


let t_binders : term = (tconst FStar_Parser_Const.binders_lid)


let t_bv : term = (tconst FStar_Parser_Const.bv_lid)


let t_fv : term = (tconst FStar_Parser_Const.fv_lid)


let t_norm_step : term = (tconst FStar_Parser_Const.norm_step_lid)


let t_tactic_unit : term = (

let uu____10001 = (

let uu____10006 = (

let uu____10007 = (tabbrev FStar_Parser_Const.tactic_lid)
in (mk_Tm_uinst uu____10007 ((U_zero)::[])))
in (

let uu____10008 = (

let uu____10009 = (as_arg t_unit)
in (uu____10009)::[])
in (mk_Tm_app uu____10006 uu____10008)))
in (uu____10001 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let t_list_of : term  ->  term = (fun t -> (

let uu____10040 = (

let uu____10045 = (

let uu____10046 = (tabbrev FStar_Parser_Const.list_lid)
in (mk_Tm_uinst uu____10046 ((U_zero)::[])))
in (

let uu____10047 = (

let uu____10048 = (as_arg t)
in (uu____10048)::[])
in (mk_Tm_app uu____10045 uu____10047)))
in (uu____10040 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let t_option_of : term  ->  term = (fun t -> (

let uu____10079 = (

let uu____10084 = (

let uu____10085 = (tabbrev FStar_Parser_Const.option_lid)
in (mk_Tm_uinst uu____10085 ((U_zero)::[])))
in (

let uu____10086 = (

let uu____10087 = (as_arg t)
in (uu____10087)::[])
in (mk_Tm_app uu____10084 uu____10086)))
in (uu____10079 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let t_tuple2_of : term  ->  term  ->  term = (fun t1 t2 -> (

let uu____10123 = (

let uu____10128 = (

let uu____10129 = (tabbrev FStar_Parser_Const.lid_tuple2)
in (mk_Tm_uinst uu____10129 ((U_zero)::(U_zero)::[])))
in (

let uu____10130 = (

let uu____10131 = (as_arg t1)
in (

let uu____10140 = (

let uu____10151 = (as_arg t2)
in (uu____10151)::[])
in (uu____10131)::uu____10140))
in (mk_Tm_app uu____10128 uu____10130)))
in (uu____10123 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let t_either_of : term  ->  term  ->  term = (fun t1 t2 -> (

let uu____10195 = (

let uu____10200 = (

let uu____10201 = (tabbrev FStar_Parser_Const.either_lid)
in (mk_Tm_uinst uu____10201 ((U_zero)::(U_zero)::[])))
in (

let uu____10202 = (

let uu____10203 = (as_arg t1)
in (

let uu____10212 = (

let uu____10223 = (as_arg t2)
in (uu____10223)::[])
in (uu____10203)::uu____10212))
in (mk_Tm_app uu____10200 uu____10202)))
in (uu____10195 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let unit_const : term = (mk (Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)




