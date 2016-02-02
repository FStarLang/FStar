
open Prims
exception Err of (Prims.string)

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_31_6) -> begin
_31_6
end))

exception Error of ((Prims.string * FStar_Range.range))

let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

let ___Error____0 = (fun projectee -> (match (projectee) with
| Error (_31_8) -> begin
_31_8
end))

exception Warning of ((Prims.string * FStar_Range.range))

let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

let ___Warning____0 = (fun projectee -> (match (projectee) with
| Warning (_31_10) -> begin
_31_10
end))

type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}

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

let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions -> begin
true
end
| _ -> begin
false
end))

let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_31_20) -> begin
_31_20
end))

type 'a memo =
'a Prims.option FStar_ST.ref

type arg_qualifier =
| Implicit
| Equality

let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit -> begin
true
end
| _ -> begin
false
end))

let is_Equality = (fun _discr_ -> (match (_discr_) with
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

let is_U_zero = (fun _discr_ -> (match (_discr_) with
| U_zero -> begin
true
end
| _ -> begin
false
end))

let is_U_succ = (fun _discr_ -> (match (_discr_) with
| U_succ (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_max = (fun _discr_ -> (match (_discr_) with
| U_max (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_bvar = (fun _discr_ -> (match (_discr_) with
| U_bvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_name = (fun _discr_ -> (match (_discr_) with
| U_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_unif = (fun _discr_ -> (match (_discr_) with
| U_unif (_) -> begin
true
end
| _ -> begin
false
end))

let is_U_unknown = (fun _discr_ -> (match (_discr_) with
| U_unknown -> begin
true
end
| _ -> begin
false
end))

let ___U_succ____0 = (fun projectee -> (match (projectee) with
| U_succ (_31_24) -> begin
_31_24
end))

let ___U_max____0 = (fun projectee -> (match (projectee) with
| U_max (_31_27) -> begin
_31_27
end))

let ___U_bvar____0 = (fun projectee -> (match (projectee) with
| U_bvar (_31_30) -> begin
_31_30
end))

let ___U_name____0 = (fun projectee -> (match (projectee) with
| U_name (_31_33) -> begin
_31_33
end))

let ___U_unif____0 = (fun projectee -> (match (projectee) with
| U_unif (_31_36) -> begin
_31_36
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
{free_names : bv FStar_Util.set; free_uvars : (uvar * typ) FStar_Util.set; free_univs : universe_uvar FStar_Util.set} 
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

let is_Tm_bvar = (fun _discr_ -> (match (_discr_) with
| Tm_bvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_name = (fun _discr_ -> (match (_discr_) with
| Tm_name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_fvar = (fun _discr_ -> (match (_discr_) with
| Tm_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_uinst = (fun _discr_ -> (match (_discr_) with
| Tm_uinst (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_constant = (fun _discr_ -> (match (_discr_) with
| Tm_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_type = (fun _discr_ -> (match (_discr_) with
| Tm_type (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_abs = (fun _discr_ -> (match (_discr_) with
| Tm_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_arrow = (fun _discr_ -> (match (_discr_) with
| Tm_arrow (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_refine = (fun _discr_ -> (match (_discr_) with
| Tm_refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_app = (fun _discr_ -> (match (_discr_) with
| Tm_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_match = (fun _discr_ -> (match (_discr_) with
| Tm_match (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_ascribed = (fun _discr_ -> (match (_discr_) with
| Tm_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_let = (fun _discr_ -> (match (_discr_) with
| Tm_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_uvar = (fun _discr_ -> (match (_discr_) with
| Tm_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_delayed = (fun _discr_ -> (match (_discr_) with
| Tm_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_meta = (fun _discr_ -> (match (_discr_) with
| Tm_meta (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tm_unknown = (fun _discr_ -> (match (_discr_) with
| Tm_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Pat_constant = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_cons = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_var = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_wild = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_dot_term = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkletbinding = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

let is_Mkcomp_typ = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

let is_GTotal = (fun _discr_ -> (match (_discr_) with
| GTotal (_) -> begin
true
end
| _ -> begin
false
end))

let is_Comp = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

let is_TOTAL = (fun _discr_ -> (match (_discr_) with
| TOTAL -> begin
true
end
| _ -> begin
false
end))

let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT -> begin
true
end
| _ -> begin
false
end))

let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN -> begin
true
end
| _ -> begin
false
end))

let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN -> begin
true
end
| _ -> begin
false
end))

let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL -> begin
true
end
| _ -> begin
false
end))

let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA -> begin
true
end
| _ -> begin
false
end))

let is_DECREASES = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_pattern = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_named = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_labeled = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_desugared = (fun _discr_ -> (match (_discr_) with
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

let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app -> begin
true
end
| _ -> begin
false
end))

let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence -> begin
true
end
| _ -> begin
false
end))

let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop -> begin
true
end
| _ -> begin
false
end))

let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect -> begin
true
end
| _ -> begin
false
end))

let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat -> begin
true
end
| _ -> begin
false
end))

let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor -> begin
true
end
| _ -> begin
false
end))

let is_Record_projector = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

let is_Record_ctor = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

let is_DB = (fun _discr_ -> (match (_discr_) with
| DB (_) -> begin
true
end
| _ -> begin
false
end))

let is_NM = (fun _discr_ -> (match (_discr_) with
| NM (_) -> begin
true
end
| _ -> begin
false
end))

let is_NT = (fun _discr_ -> (match (_discr_) with
| NT (_) -> begin
true
end
| _ -> begin
false
end))

let is_UN = (fun _discr_ -> (match (_discr_) with
| UN (_) -> begin
true
end
| _ -> begin
false
end))

let is_UD = (fun _discr_ -> (match (_discr_) with
| UD (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

let is_Mkbv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbv"))))

let is_Mkfree_vars = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfree_vars"))))

let is_Mklcomp = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

let ___Tm_bvar____0 = (fun projectee -> (match (projectee) with
| Tm_bvar (_31_65) -> begin
_31_65
end))

let ___Tm_name____0 = (fun projectee -> (match (projectee) with
| Tm_name (_31_68) -> begin
_31_68
end))

let ___Tm_fvar____0 = (fun projectee -> (match (projectee) with
| Tm_fvar (_31_71) -> begin
_31_71
end))

let ___Tm_uinst____0 = (fun projectee -> (match (projectee) with
| Tm_uinst (_31_74) -> begin
_31_74
end))

let ___Tm_constant____0 = (fun projectee -> (match (projectee) with
| Tm_constant (_31_77) -> begin
_31_77
end))

let ___Tm_type____0 = (fun projectee -> (match (projectee) with
| Tm_type (_31_80) -> begin
_31_80
end))

let ___Tm_abs____0 = (fun projectee -> (match (projectee) with
| Tm_abs (_31_83) -> begin
_31_83
end))

let ___Tm_arrow____0 = (fun projectee -> (match (projectee) with
| Tm_arrow (_31_86) -> begin
_31_86
end))

let ___Tm_refine____0 = (fun projectee -> (match (projectee) with
| Tm_refine (_31_89) -> begin
_31_89
end))

let ___Tm_app____0 = (fun projectee -> (match (projectee) with
| Tm_app (_31_92) -> begin
_31_92
end))

let ___Tm_match____0 = (fun projectee -> (match (projectee) with
| Tm_match (_31_95) -> begin
_31_95
end))

let ___Tm_ascribed____0 = (fun projectee -> (match (projectee) with
| Tm_ascribed (_31_98) -> begin
_31_98
end))

let ___Tm_let____0 = (fun projectee -> (match (projectee) with
| Tm_let (_31_101) -> begin
_31_101
end))

let ___Tm_uvar____0 = (fun projectee -> (match (projectee) with
| Tm_uvar (_31_104) -> begin
_31_104
end))

let ___Tm_delayed____0 = (fun projectee -> (match (projectee) with
| Tm_delayed (_31_107) -> begin
_31_107
end))

let ___Tm_meta____0 = (fun projectee -> (match (projectee) with
| Tm_meta (_31_110) -> begin
_31_110
end))

let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_31_113) -> begin
_31_113
end))

let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_31_116) -> begin
_31_116
end))

let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_31_119) -> begin
_31_119
end))

let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_31_122) -> begin
_31_122
end))

let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_31_125) -> begin
_31_125
end))

let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_31_128) -> begin
_31_128
end))

let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_31_133) -> begin
_31_133
end))

let ___GTotal____0 = (fun projectee -> (match (projectee) with
| GTotal (_31_136) -> begin
_31_136
end))

let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_31_139) -> begin
_31_139
end))

let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_31_142) -> begin
_31_142
end))

let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_31_145) -> begin
_31_145
end))

let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_31_148) -> begin
_31_148
end))

let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_31_151) -> begin
_31_151
end))

let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_31_154) -> begin
_31_154
end))

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_31_157) -> begin
_31_157
end))

let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_31_160) -> begin
_31_160
end))

let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_31_163) -> begin
_31_163
end))

let ___DB____0 = (fun projectee -> (match (projectee) with
| DB (_31_166) -> begin
_31_166
end))

let ___NM____0 = (fun projectee -> (match (projectee) with
| NM (_31_169) -> begin
_31_169
end))

let ___NT____0 = (fun projectee -> (match (projectee) with
| NT (_31_172) -> begin
_31_172
end))

let ___UN____0 = (fun projectee -> (match (projectee) with
| UN (_31_175) -> begin
_31_175
end))

let ___UD____0 = (fun projectee -> (match (projectee) with
| UD (_31_178) -> begin
_31_178
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

let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_New = (fun _discr_ -> (match (_discr_) with
| New -> begin
true
end
| _ -> begin
false
end))

let is_Private = (fun _discr_ -> (match (_discr_) with
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline -> begin
true
end
| _ -> begin
false
end))

let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable -> begin
true
end
| _ -> begin
false
end))

let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible -> begin
true
end
| _ -> begin
false
end))

let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract -> begin
true
end
| _ -> begin
false
end))

let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect -> begin
true
end
| _ -> begin
false
end))

let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic -> begin
true
end
| _ -> begin
false
end))

let is_Discriminator = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

let is_RecordType = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

let is_RecordConstructor = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor -> begin
true
end
| _ -> begin
false
end))

let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))

let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect -> begin
true
end
| _ -> begin
false
end))

let ___DefaultEffect____0 = (fun projectee -> (match (projectee) with
| DefaultEffect (_31_185) -> begin
_31_185
end))

let ___Discriminator____0 = (fun projectee -> (match (projectee) with
| Discriminator (_31_188) -> begin
_31_188
end))

let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_31_191) -> begin
_31_191
end))

let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_31_194) -> begin
_31_194
end))

let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_31_197) -> begin
_31_197
end))

type tycon =
(FStar_Ident.lident * binders * typ)

type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}

let is_Mkmonad_abbrev = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift : tscheme}

let is_Mksub_eff = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

type eff_decl =
{qualifiers : qualifier Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret : tscheme; bind_wp : tscheme; bind_wlp : tscheme; if_then_else : tscheme; ite_wp : tscheme; ite_wlp : tscheme; wp_binop : tscheme; wp_as_type : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme} 
 and sigelt =
| Sig_inductive_typ of (FStar_Ident.lident, univ_names, binders, typ, FStar_Ident.lident Prims.list, FStar_Ident.lident Prims.list, qualifier Prims.list, FStar_Range.range) Prims.l__Tuple8
| Sig_bundle of (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_datacon of (FStar_Ident.lident, univ_names, typ, FStar_Ident.lident, Prims.int, qualifier Prims.list, FStar_Ident.lident Prims.list, FStar_Range.range) Prims.l__Tuple8
| Sig_declare_typ of (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range)
| Sig_let of (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list)
| Sig_main of (term * FStar_Range.range)
| Sig_assume of (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range)
| Sig_new_effect of (eff_decl * FStar_Range.range)
| Sig_sub_effect of (sub_eff * FStar_Range.range)
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range)
| Sig_pragma of (pragma * FStar_Range.range)

let is_Mkeff_decl = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

let is_Sig_inductive_typ = (fun _discr_ -> (match (_discr_) with
| Sig_inductive_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_datacon = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_declare_typ = (fun _discr_ -> (match (_discr_) with
| Sig_declare_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_let = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_main = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_assume = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_new_effect = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_sub_effect = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_effect_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_pragma = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

let ___Sig_inductive_typ____0 = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_31_227) -> begin
_31_227
end))

let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_31_230) -> begin
_31_230
end))

let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_31_233) -> begin
_31_233
end))

let ___Sig_declare_typ____0 = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_31_236) -> begin
_31_236
end))

let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_31_239) -> begin
_31_239
end))

let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_31_242) -> begin
_31_242
end))

let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_31_245) -> begin
_31_245
end))

let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_31_248) -> begin
_31_248
end))

let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_31_251) -> begin
_31_251
end))

let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_31_254) -> begin
_31_254
end))

let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_31_257) -> begin
_31_257
end))

type sigelts =
sigelt Prims.list

type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}

let is_Mkmodul = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

type path =
Prims.string Prims.list

type subst_t =
subst_elt Prims.list

type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax

type mk_t =
(term', term') mk_t_a

let withinfo = (fun v s r -> {v = v; sort = s; p = r})

let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))

let bv_eq = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))

let order_bv = (fun x y -> (let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = 0) then begin
(x.index - y.index)
end else begin
i
end))

let range_of_lbname = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(FStar_Ident.range_of_lid l)
end))

let range_of_bv = (fun x -> x.ppname.FStar_Ident.idRange)

let set_range_of_bv = (fun x r -> (let _31_283 = x
in {ppname = (FStar_Ident.mk_ident (x.ppname.FStar_Ident.idText, r)); index = _31_283.index; sort = _31_283.sort}))

let syn = (fun p k f -> (f k p))

let mk_fvs = (fun _31_288 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let mk_uvs = (fun _31_289 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let new_bv_set = (fun _31_290 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))

let new_uv_set = (fun _31_292 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _31_300 _31_304 -> (match ((_31_300, _31_304)) with
| ((x, _31_299), (y, _31_303)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _31_296 -> (match (_31_296) with
| (x, _31_295) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

let new_universe_uvar_set = (fun _31_305 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))

let no_names = (new_bv_set ())

let no_uvs = (new_uv_set ())

let no_universe_uvars = (new_universe_uvar_set ())

let memo_no_uvs = (FStar_Util.mk_ref (Some (no_uvs)))

let memo_no_names = (FStar_Util.mk_ref (Some (no_names)))

let freenames_of_list = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))

let list_of_freenames = (fun fvs -> (FStar_Util.set_elements fvs))

let mk = (fun t topt r -> (let _84_1153 = (FStar_Util.mk_ref topt)
in (let _84_1152 = (FStar_Util.mk_ref None)
in {n = t; tk = _84_1153; pos = r; vars = _84_1152})))

let bv_to_tm = (fun bv -> (let _84_1156 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (Some (bv.sort.n)) _84_1156)))

let bv_to_name = (fun bv -> (let _84_1159 = (range_of_bv bv)
in (mk (Tm_name (bv)) (Some (bv.sort.n)) _84_1159)))

let mk_Tm_app = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _31_324 -> begin
(mk (Tm_app ((t1, args))) k p)
end))

let mk_Tm_uinst = (fun t _31_1 -> (match (_31_1) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_31_330) -> begin
(mk (Tm_uinst ((t, us))) None t.pos)
end
| _31_333 -> begin
(FStar_All.failwith "Unexpected universe instantiation")
end)
end))

let extend_app_n = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _31_343 -> begin
(mk_Tm_app t args' kopt r)
end))

let extend_app = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))

let mk_Tm_delayed = (fun lr pos -> (let _84_1194 = (let _84_1193 = (let _84_1192 = (FStar_Util.mk_ref None)
in (lr, _84_1192))
in Tm_delayed (_84_1193))
in (mk _84_1194 None pos)))

let mk_Total = (fun t -> (mk (Total (t)) None t.pos))

let mk_GTotal = (fun t -> (mk (GTotal (t)) None t.pos))

let mk_Comp = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))

let mk_lb = (fun _31_358 -> (match (_31_358) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst = (fun s -> s)

let extend_subst = (fun x s -> (x)::s)

let argpos = (fun x -> (Prims.fst x).pos)

let tun = (mk Tm_unknown None FStar_Range.dummyRange)

let teff = (mk (Tm_constant (FStar_Const.Const_effect)) None FStar_Range.dummyRange)

let is_teff = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| _31_367 -> begin
false
end))

let is_type = (fun t -> (match (t.n) with
| Tm_type (_31_370) -> begin
true
end
| _31_373 -> begin
false
end))

let null_id = (FStar_Ident.mk_ident ("_", FStar_Range.dummyRange))

let null_bv = (fun k -> {ppname = null_id; index = 0; sort = k})

let mk_binder = (fun a -> (a, None))

let null_binder = (fun t -> (let _84_1221 = (null_bv t)
in (_84_1221, None)))

let iarg = (fun t -> (t, Some (Implicit)))

let as_arg = (fun t -> (t, None))

let is_null_bv = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

let is_null_binder = (fun b -> (is_null_bv (Prims.fst b)))

let freenames_of_binders = (fun bs -> (FStar_List.fold_right (fun _31_385 out -> (match (_31_385) with
| (x, _31_384) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))

let binders_of_list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

let binders_of_freenames = (fun fvs -> (let _84_1239 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _84_1239 binders_of_list)))

let is_implicit = (fun _31_2 -> (match (_31_2) with
| Some (Implicit) -> begin
true
end
| _31_394 -> begin
false
end))

let as_implicit = (fun _31_3 -> (match (_31_3) with
| true -> begin
Some (Implicit)
end
| _31_398 -> begin
None
end))

let pat_bvs = (fun p -> (let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (_31_413, pats) -> begin
(FStar_List.fold_left (fun b _31_421 -> (match (_31_421) with
| (p, _31_420) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj (p::_31_423) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (aux [] p)))

let gen_reset = (let x = (FStar_ST.alloc 0)
in (let gen = (fun _31_431 -> (match (()) with
| () -> begin
(let _31_432 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (let reset = (fun _31_435 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x 0)
end))
in (gen, reset))))

let next_id = (Prims.fst gen_reset)

let reset_gensym = (Prims.snd gen_reset)

let freshen_bv = (fun bv -> (let _31_437 = bv
in (let _84_1270 = (next_id ())
in {ppname = _31_437.ppname; index = _84_1270; sort = _31_437.sort})))

let range_of_ropt = (fun _31_4 -> (match (_31_4) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))

let gen_bv = (fun s r t -> (let id = (FStar_Ident.mk_ident (s, (range_of_ropt r)))
in (let _84_1279 = (next_id ())
in {ppname = id; index = _84_1279; sort = t})))

let new_bv = (fun ropt t -> (gen_bv "x" ropt t))

let new_univ_name = (fun ropt -> (let id = (next_id ())
in (let _84_1287 = (let _84_1286 = (FStar_Util.string_of_int id)
in (_84_1286, (range_of_ropt ropt)))
in (FStar_Ident.mk_ident _84_1287))))

let mkbv = (fun x y t -> {ppname = x; index = y; sort = t})

let lbname_eq = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _31_467 -> begin
false
end))

let fv_eq = (fun _31_471 _31_475 -> (match ((_31_471, _31_475)) with
| ((fv1, _31_470), (fv2, _31_474)) -> begin
(FStar_Ident.lid_equals fv1.v fv2.v)
end))

let set_bv_range = (fun bv r -> (let _31_478 = bv
in {ppname = (FStar_Ident.mk_ident (bv.ppname.FStar_Ident.idText, r)); index = _31_478.index; sort = _31_478.sort}))

let lid_as_fv = (fun l dc -> (let _84_1310 = (withinfo l tun (FStar_Ident.range_of_lid l))
in (_84_1310, dc)))

let fv_to_tm = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid (Prims.fst fv).v)))

let fvar = (fun dc l r -> (let _84_1321 = (let _84_1320 = (let _84_1319 = (FStar_Ident.set_lid_range l r)
in (lid_as_fv _84_1319 dc))
in Tm_fvar (_84_1320))
in (mk _84_1321 None r)))




