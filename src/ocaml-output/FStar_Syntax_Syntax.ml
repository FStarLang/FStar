
open Prims
exception Err of (Prims.string)

let is_Err : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_33_6) -> begin
_33_6
end))

exception Error of ((Prims.string * FStar_Range.range))

let is_Error : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

let ___Error____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (_33_8) -> begin
_33_8
end))

exception Warning of ((Prims.string * FStar_Range.range))

let is_Warning : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

let ___Warning____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (_33_10) -> begin
_33_10
end))

type ('a, 't) withinfo_t =
{v : 'a; ty : 't; p : FStar_Range.range}

let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

type 't var =
(FStar_Ident.lident, 't) withinfo_t

type fieldname =
FStar_Ident.lident

type sconst =
FStar_Const.sconst

type pragma =
| SetOptions of Prims.string
| ResetOptions

let is_SetOptions : pragma  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

let is_ResetOptions : pragma  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ResetOptions -> begin
true
end
| _ -> begin
false
end))

let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_33_20) -> begin
_33_20
end))

type 'a memo =
'a Prims.option FStar_ST.ref

type arg_qualifier =
| Implicit
| Equality

let is_Implicit : arg_qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Implicit -> begin
true
end
| _ -> begin
false
end))

let is_Equality : arg_qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Equality -> begin
true
end
| _ -> begin
false
end))

type aqual =
arg_qualifier Prims.option

type universe =
| U_zero
| U_succ of universe
| U_max of universe Prims.list
| U_bvar of Prims.int
| U_name of univ_name
| U_unif of universe Prims.option FStar_Unionfind.uvar
| U_unknown 
 and univ_name =
FStar_Ident.ident

let is_U_zero : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_zero -> begin
true
end
| _ -> begin
false
end))

let is_U_succ : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_succ (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_max : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_max (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_bvar : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_bvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_name : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_unif : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_unif (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_unknown : universe  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| U_unknown -> begin
true
end
| _ -> begin
false
end))

let ___U_succ____0 : universe  ->  universe = (fun projectee -> (match (projectee) with
| U_succ (_33_24) -> begin
_33_24
end))

let ___U_max____0 : universe  ->  universe Prims.list = (fun projectee -> (match (projectee) with
| U_max (_33_27) -> begin
_33_27
end))

let ___U_bvar____0 : universe  ->  Prims.int = (fun projectee -> (match (projectee) with
| U_bvar (_33_30) -> begin
_33_30
end))

let ___U_name____0 : universe  ->  univ_name = (fun projectee -> (match (projectee) with
| U_name (_33_33) -> begin
_33_33
end))

let ___U_unif____0 : universe  ->  universe Prims.option FStar_Unionfind.uvar = (fun projectee -> (match (projectee) with
| U_unif (_33_36) -> begin
_33_36
end))

type universe_uvar =
universe Prims.option FStar_Unionfind.uvar

type univ_names =
univ_name Prims.list

type universes =
universe Prims.list

type term' =
| Tm_bvar of bv
| Tm_name of bv
| Tm_fvar of fv
| Tm_uinst of (term * universes)
| Tm_constant of sconst
| Tm_type of universe
| Tm_abs of (binders * term * lcomp Prims.option)
| Tm_arrow of (binders * comp)
| Tm_refine of (bv * term)
| Tm_app of (term * args)
| Tm_match of (term * branch Prims.list)
| Tm_ascribed of (term * term * FStar_Ident.lident Prims.option)
| Tm_let of (letbindings * term)
| Tm_uvar of (uvar * term)
| Tm_delayed of (((term * subst_ts), Prims.unit  ->  term) FStar_Util.either * term memo)
| Tm_meta of (term * metadata)
| Tm_unknown 
 and pat' =
| Pat_constant of sconst
| Pat_disj of pat Prims.list
| Pat_cons of (fv * (pat * Prims.bool) Prims.list)
| Pat_var of bv
| Pat_wild of bv
| Pat_dot_term of (bv * term) 
 and letbinding =
{lbname : lbname; lbunivs : univ_name Prims.list; lbtyp : typ; lbeff : FStar_Ident.lident; lbdef : term} 
 and comp_typ =
{effect_name : FStar_Ident.lident; result_typ : typ; effect_args : args; flags : cflags Prims.list} 
 and comp' =
| Total of typ
| GTotal of typ
| Comp of comp_typ 
 and cflags =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| LEMMA
| DECREASES of term 
 and metadata =
| Meta_pattern of args Prims.list
| Meta_named of FStar_Ident.lident
| Meta_labeled of (Prims.string * FStar_Range.range * Prims.bool)
| Meta_desugared of meta_source_info 
 and 'a uvar_basis =
| Uvar
| Fixed of 'a 
 and meta_source_info =
| Data_app
| Sequence
| Primop
| Masked_effect
| Meta_smt_pat 
 and fv_qual =
| Data_ctor
| Record_projector of FStar_Ident.lident
| Record_ctor of (FStar_Ident.lident * fieldname Prims.list) 
 and subst_elt =
| DB of (Prims.int * term)
| NM of (bv * Prims.int)
| NT of (bv * term)
| UN of (Prims.int * universe)
| UD of (univ_name * Prims.int) 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : FStar_Range.range; vars : free_vars memo} 
 and bv =
{ppname : FStar_Ident.ident; index : Prims.int; sort : term} 
 and free_vars =
{free_names : bv FStar_Util.set; free_uvars : uvars; free_univs : universe_uvar FStar_Util.set} 
 and lcomp =
{eff_name : FStar_Ident.lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp} 
 and branch =
(pat * term Prims.option * term) 
 and term =
(term', term') syntax 
 and typ =
term 
 and pat =
(pat', term') withinfo_t 
 and comp =
(comp', Prims.unit) syntax 
 and arg =
(term * aqual) 
 and args =
arg Prims.list 
 and binder =
(bv * aqual) 
 and binders =
binder Prims.list 
 and uvar =
term uvar_basis FStar_Unionfind.uvar 
 and lbname =
(bv, FStar_Ident.lident) FStar_Util.either 
 and letbindings =
(Prims.bool * letbinding Prims.list) 
 and subst_ts =
subst_elt Prims.list Prims.list 
 and freenames =
bv FStar_Util.set 
 and uvars =
(uvar * typ) FStar_Util.set 
 and fv =
(term var * fv_qual Prims.option)

let is_Tm_bvar : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_bvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_name : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_fvar : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_uinst : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_uinst (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_constant : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_type : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_type (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_abs : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_arrow : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_arrow (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_refine : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_app : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_match : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_match (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_ascribed : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_let : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_uvar : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_delayed : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_meta : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_meta (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_unknown : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tm_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Pat_constant : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_disj : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_cons : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_var : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_wild : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_dot_term : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

let is_Total : comp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

let is_GTotal : comp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| GTotal (_) -> begin
true
end
| _ -> begin
false
end))

let is_Comp : comp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

let is_TOTAL : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TOTAL -> begin
true
end
| _ -> begin
false
end))

let is_MLEFFECT : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MLEFFECT -> begin
true
end
| _ -> begin
false
end))

let is_RETURN : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| RETURN -> begin
true
end
| _ -> begin
false
end))

let is_PARTIAL_RETURN : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN -> begin
true
end
| _ -> begin
false
end))

let is_SOMETRIVIAL : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL -> begin
true
end
| _ -> begin
false
end))

let is_LEMMA : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| LEMMA -> begin
true
end
| _ -> begin
false
end))

let is_DECREASES : cflags  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_pattern : metadata  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_named : metadata  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_labeled : metadata  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_desugared : metadata  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

let is_Uvar = (fun _discr_ -> (match (_discr_) with
| Uvar -> begin
true
end
| _ -> begin
false
end))

let is_Fixed = (fun _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Data_app : meta_source_info  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Data_app -> begin
true
end
| _ -> begin
false
end))

let is_Sequence : meta_source_info  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sequence -> begin
true
end
| _ -> begin
false
end))

let is_Primop : meta_source_info  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Primop -> begin
true
end
| _ -> begin
false
end))

let is_Masked_effect : meta_source_info  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Masked_effect -> begin
true
end
| _ -> begin
false
end))

let is_Meta_smt_pat : meta_source_info  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat -> begin
true
end
| _ -> begin
false
end))

let is_Data_ctor : fv_qual  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Data_ctor -> begin
true
end
| _ -> begin
false
end))

let is_Record_projector : fv_qual  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

let is_Record_ctor : fv_qual  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

let is_DB : subst_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DB (_) -> begin
true
end
| _ -> begin
false
end))

let is_NM : subst_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NM (_) -> begin
true
end
| _ -> begin
false
end))

let is_NT : subst_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NT (_) -> begin
true
end
| _ -> begin
false
end))

let is_UN : subst_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UN (_) -> begin
true
end
| _ -> begin
false
end))

let is_UD : subst_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UD (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

let is_Mkbv : bv  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbv"))))

let is_Mkfree_vars : free_vars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfree_vars"))))

let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

let ___Tm_bvar____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_bvar (_33_65) -> begin
_33_65
end))

let ___Tm_name____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_name (_33_68) -> begin
_33_68
end))

let ___Tm_fvar____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| Tm_fvar (_33_71) -> begin
_33_71
end))

let ___Tm_uinst____0 : term'  ->  (term * universes) = (fun projectee -> (match (projectee) with
| Tm_uinst (_33_74) -> begin
_33_74
end))

let ___Tm_constant____0 : term'  ->  sconst = (fun projectee -> (match (projectee) with
| Tm_constant (_33_77) -> begin
_33_77
end))

let ___Tm_type____0 : term'  ->  universe = (fun projectee -> (match (projectee) with
| Tm_type (_33_80) -> begin
_33_80
end))

let ___Tm_abs____0 : term'  ->  (binders * term * lcomp Prims.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_33_83) -> begin
_33_83
end))

let ___Tm_arrow____0 : term'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Tm_arrow (_33_86) -> begin
_33_86
end))

let ___Tm_refine____0 : term'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Tm_refine (_33_89) -> begin
_33_89
end))

let ___Tm_app____0 : term'  ->  (term * args) = (fun projectee -> (match (projectee) with
| Tm_app (_33_92) -> begin
_33_92
end))

let ___Tm_match____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_33_95) -> begin
_33_95
end))

let ___Tm_ascribed____0 : term'  ->  (term * term * FStar_Ident.lident Prims.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_33_98) -> begin
_33_98
end))

let ___Tm_let____0 : term'  ->  (letbindings * term) = (fun projectee -> (match (projectee) with
| Tm_let (_33_101) -> begin
_33_101
end))

let ___Tm_uvar____0 : term'  ->  (uvar * term) = (fun projectee -> (match (projectee) with
| Tm_uvar (_33_104) -> begin
_33_104
end))

let ___Tm_delayed____0 : term'  ->  (((term * subst_ts), Prims.unit  ->  term) FStar_Util.either * term memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_33_107) -> begin
_33_107
end))

let ___Tm_meta____0 : term'  ->  (term * metadata) = (fun projectee -> (match (projectee) with
| Tm_meta (_33_110) -> begin
_33_110
end))

let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_33_113) -> begin
_33_113
end))

let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_33_116) -> begin
_33_116
end))

let ___Pat_cons____0 : pat'  ->  (fv * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_33_119) -> begin
_33_119
end))

let ___Pat_var____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_var (_33_122) -> begin
_33_122
end))

let ___Pat_wild____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_wild (_33_125) -> begin
_33_125
end))

let ___Pat_dot_term____0 : pat'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_33_128) -> begin
_33_128
end))

let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_33_133) -> begin
_33_133
end))

let ___GTotal____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| GTotal (_33_136) -> begin
_33_136
end))

let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_33_139) -> begin
_33_139
end))

let ___DECREASES____0 : cflags  ->  term = (fun projectee -> (match (projectee) with
| DECREASES (_33_142) -> begin
_33_142
end))

let ___Meta_pattern____0 : metadata  ->  args Prims.list = (fun projectee -> (match (projectee) with
| Meta_pattern (_33_145) -> begin
_33_145
end))

let ___Meta_named____0 : metadata  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Meta_named (_33_148) -> begin
_33_148
end))

let ___Meta_labeled____0 : metadata  ->  (Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_33_151) -> begin
_33_151
end))

let ___Meta_desugared____0 : metadata  ->  meta_source_info = (fun projectee -> (match (projectee) with
| Meta_desugared (_33_154) -> begin
_33_154
end))

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_33_157) -> begin
_33_157
end))

let ___Record_projector____0 : fv_qual  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Record_projector (_33_160) -> begin
_33_160
end))

let ___Record_ctor____0 : fv_qual  ->  (FStar_Ident.lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_33_163) -> begin
_33_163
end))

let ___DB____0 : subst_elt  ->  (Prims.int * term) = (fun projectee -> (match (projectee) with
| DB (_33_166) -> begin
_33_166
end))

let ___NM____0 : subst_elt  ->  (bv * Prims.int) = (fun projectee -> (match (projectee) with
| NM (_33_169) -> begin
_33_169
end))

let ___NT____0 : subst_elt  ->  (bv * term) = (fun projectee -> (match (projectee) with
| NT (_33_172) -> begin
_33_172
end))

let ___UN____0 : subst_elt  ->  (Prims.int * universe) = (fun projectee -> (match (projectee) with
| UN (_33_175) -> begin
_33_175
end))

let ___UD____0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_33_178) -> begin
_33_178
end))

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
| Inline
| Unfoldable
| Irreducible
| Abstract
| DefaultEffect of FStar_Ident.lident Prims.option
| TotalEffect
| Logic
| Discriminator of FStar_Ident.lident
| Projector of (FStar_Ident.lident * FStar_Ident.ident)
| RecordType of fieldname Prims.list
| RecordConstructor of fieldname Prims.list
| ExceptionConstructor
| HasMaskedEffect
| Effect

let is_Assumption : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_New : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| New -> begin
true
end
| _ -> begin
false
end))

let is_Private : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Inline : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Inline -> begin
true
end
| _ -> begin
false
end))

let is_Unfoldable : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Unfoldable -> begin
true
end
| _ -> begin
false
end))

let is_Irreducible : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Irreducible -> begin
true
end
| _ -> begin
false
end))

let is_Abstract : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Abstract -> begin
true
end
| _ -> begin
false
end))

let is_DefaultEffect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_TotalEffect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TotalEffect -> begin
true
end
| _ -> begin
false
end))

let is_Logic : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Logic -> begin
true
end
| _ -> begin
false
end))

let is_Discriminator : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

let is_Projector : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

let is_RecordType : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

let is_RecordConstructor : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

let is_ExceptionConstructor : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor -> begin
true
end
| _ -> begin
false
end))

let is_HasMaskedEffect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))

let is_Effect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Effect -> begin
true
end
| _ -> begin
false
end))

let ___DefaultEffect____0 : qualifier  ->  FStar_Ident.lident Prims.option = (fun projectee -> (match (projectee) with
| DefaultEffect (_33_185) -> begin
_33_185
end))

let ___Discriminator____0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Discriminator (_33_188) -> begin
_33_188
end))

let ___Projector____0 : qualifier  ->  (FStar_Ident.lident * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_33_191) -> begin
_33_191
end))

let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_33_194) -> begin
_33_194
end))

let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_33_197) -> begin
_33_197
end))

type tycon =
(FStar_Ident.lident * binders * typ)

type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}

let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift : tscheme}

let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

type eff_decl =
{qualifiers : qualifier Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret : tscheme; bind_wp : tscheme; bind_wlp : tscheme; if_then_else : tscheme; ite_wp : tscheme; ite_wlp : tscheme; wp_binop : tscheme; wp_as_type : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme} 
 and sigelt =
| Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range)
| Sig_bundle of (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_datacon of (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_declare_typ of (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range)
| Sig_let of (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list)
| Sig_main of (term * FStar_Range.range)
| Sig_assume of (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range)
| Sig_new_effect of (eff_decl * FStar_Range.range)
| Sig_sub_effect of (sub_eff * FStar_Range.range)
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range)
| Sig_pragma of (pragma * FStar_Range.range)

let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

let is_Sig_inductive_typ : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_inductive_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_bundle : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_datacon : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_declare_typ : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_declare_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_let : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_main : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_assume : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_new_effect : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_sub_effect : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_effect_abbrev : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_pragma : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

let ___Sig_inductive_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_33_227) -> begin
_33_227
end))

let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_33_230) -> begin
_33_230
end))

let ___Sig_datacon____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_33_233) -> begin
_33_233
end))

let ___Sig_declare_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_33_236) -> begin
_33_236
end))

let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_33_239) -> begin
_33_239
end))

let ___Sig_main____0 : sigelt  ->  (term * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_33_242) -> begin
_33_242
end))

let ___Sig_assume____0 : sigelt  ->  (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_33_245) -> begin
_33_245
end))

let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_33_248) -> begin
_33_248
end))

let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_33_251) -> begin
_33_251
end))

let ___Sig_effect_abbrev____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_33_254) -> begin
_33_254
end))

let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_33_257) -> begin
_33_257
end))

type sigelts =
sigelt Prims.list

type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}

let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

type path =
Prims.string Prims.list

type subst_t =
subst_elt Prims.list

type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax

type mk_t =
(term', term') mk_t_a

let withinfo = (fun v s r -> {v = v; ty = s; p = r})

let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))

let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))

let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = 0) then begin
(x.index - y.index)
end else begin
i
end))

let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(FStar_Ident.range_of_lid l)
end))

let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)

let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (let _33_283 = x
in {ppname = (FStar_Ident.mk_ident (x.ppname.FStar_Ident.idText, r)); index = _33_283.index; sort = _33_283.sort}))

let syn = (fun p k f -> (f k p))

let mk_fvs = (fun _33_288 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let mk_uvs = (fun _33_289 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun _33_290 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))

let new_uv_set : Prims.unit  ->  uvars = (fun _33_292 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _33_300 _33_304 -> (match ((_33_300, _33_304)) with
| ((x, _33_299), (y, _33_303)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _33_296 -> (match (_33_296) with
| (x, _33_295) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

let new_universe_uvar_set : Prims.unit  ->  universe_uvar FStar_Util.set = (fun _33_305 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))

let no_names : freenames = (new_bv_set ())

let no_uvs : uvars = (new_uv_set ())

let no_universe_uvars : universe_uvar FStar_Util.set = (new_universe_uvar_set ())

let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars}

let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

let memo_no_names : freenames Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))

let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))

let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))

let mk = (fun t topt r -> (let _136_1153 = (FStar_Util.mk_ref topt)
in (let _136_1152 = (FStar_Util.mk_ref None)
in {n = t; tk = _136_1153; pos = r; vars = _136_1152})))

let bv_to_tm : bv  ->  term = (fun bv -> (let _136_1156 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (Some (bv.sort.n)) _136_1156)))

let bv_to_name : bv  ->  term = (fun bv -> (let _136_1159 = (range_of_bv bv)
in (mk (Tm_name (bv)) (Some (bv.sort.n)) _136_1159)))

let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _33_324 -> begin
(mk (Tm_app ((t1, args))) k p)
end))

let mk_Tm_uinst : term  ->  universes  ->  term = (fun t _33_1 -> (match (_33_1) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_33_330) -> begin
(mk (Tm_uinst ((t, us))) None t.pos)
end
| _33_333 -> begin
(FStar_All.failwith "Unexpected universe instantiation")
end)
end))

let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _33_343 -> begin
(mk_Tm_app t args' kopt r)
end))

let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))

let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  term = (fun lr pos -> (let _136_1194 = (let _136_1193 = (let _136_1192 = (FStar_Util.mk_ref None)
in (lr, _136_1192))
in Tm_delayed (_136_1193))
in (mk _136_1194 None pos)))

let mk_Total : typ  ->  comp = (fun t -> (mk (Total (t)) None t.pos))

let mk_GTotal : typ  ->  comp = (fun t -> (mk (GTotal (t)) None t.pos))

let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))

let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun _33_358 -> (match (_33_358) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst : subst_t  ->  subst_t = (fun s -> s)

let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_elt Prims.list = (fun x s -> (x)::s)

let argpos : arg  ->  FStar_Range.range = (fun x -> (Prims.fst x).pos)

let tun : (term', term') syntax = (mk Tm_unknown None FStar_Range.dummyRange)

let teff : (term', term') syntax = (mk (Tm_constant (FStar_Const.Const_effect)) (Some (Tm_unknown)) FStar_Range.dummyRange)

let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| _33_367 -> begin
false
end))

let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (_33_370) -> begin
true
end
| _33_373 -> begin
false
end))

let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident ("_", FStar_Range.dummyRange))

let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = 0; sort = k})

let mk_binder : bv  ->  binder = (fun a -> (a, None))

let null_binder : term  ->  binder = (fun t -> (let _136_1221 = (null_bv t)
in (_136_1221, None)))

let iarg : term  ->  arg = (fun t -> (t, Some (Implicit)))

let as_arg : term  ->  arg = (fun t -> (t, None))

let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))

let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun _33_385 out -> (match (_33_385) with
| (x, _33_384) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))

let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

let binders_of_freenames : freenames  ->  binders = (fun fvs -> (let _136_1239 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _136_1239 binders_of_list)))

let is_implicit : aqual  ->  Prims.bool = (fun _33_2 -> (match (_33_2) with
| Some (Implicit) -> begin
true
end
| _33_394 -> begin
false
end))

let as_implicit : Prims.bool  ->  aqual = (fun _33_3 -> (match (_33_3) with
| true -> begin
Some (Implicit)
end
| _33_398 -> begin
None
end))

let pat_bvs : pat  ->  bv Prims.list = (fun p -> (let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (_33_413, pats) -> begin
(FStar_List.fold_left (fun b _33_421 -> (match (_33_421) with
| (p, _33_420) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj (p::_33_423) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (aux [] p)))

let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (let x = (FStar_ST.alloc 0)
in (let gen = (fun _33_431 -> (match (()) with
| () -> begin
(let _33_432 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (let reset = (fun _33_435 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x 0)
end))
in (gen, reset))))

let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)

let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)

let freshen_bv : bv  ->  bv = (fun bv -> (let _33_437 = bv
in (let _136_1270 = (next_id ())
in {ppname = _33_437.ppname; index = _136_1270; sort = _33_437.sort})))

let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun _33_4 -> (match (_33_4) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))

let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (let id = (FStar_Ident.mk_ident (s, (range_of_ropt r)))
in (let _136_1279 = (next_id ())
in {ppname = id; index = _136_1279; sort = t})))

let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv "x" ropt t))

let new_univ_name : FStar_Range.range Prims.option  ->  univ_name = (fun ropt -> (let id = (next_id ())
in (let _136_1287 = (let _136_1286 = (FStar_Util.string_of_int id)
in (_136_1286, (range_of_ropt ropt)))
in (FStar_Ident.mk_ident _136_1287))))

let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})

let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _33_467 -> begin
false
end))

let fv_eq : fv  ->  fv  ->  Prims.bool = (fun _33_471 _33_475 -> (match ((_33_471, _33_475)) with
| ((fv1, _33_470), (fv2, _33_474)) -> begin
(FStar_Ident.lid_equals fv1.v fv2.v)
end))

let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (let _33_478 = bv
in {ppname = (FStar_Ident.mk_ident (bv.ppname.FStar_Ident.idText, r)); index = _33_478.index; sort = _33_478.sort}))

let lid_as_fv : FStar_Ident.lident  ->  fv_qual Prims.option  ->  fv = (fun l dc -> (let _136_1310 = (withinfo l tun (FStar_Ident.range_of_lid l))
in (_136_1310, dc)))

let fv_to_tm : fv  ->  term = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid (Prims.fst fv).v)))

let fvar : fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  term = (fun dc l r -> (let _136_1321 = (let _136_1320 = (let _136_1319 = (FStar_Ident.set_lid_range l r)
in (lid_as_fv _136_1319 dc))
in Tm_fvar (_136_1320))
in (mk _136_1321 None r)))




