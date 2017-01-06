
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
| Err (_34_9) -> begin
_34_9
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
| Error (_34_11) -> begin
_34_11
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
| Warning (_34_13) -> begin
_34_13
end))


type ('a, 't) withinfo_t =
{v : 'a; ty : 't; p : FStar_Range.range}


let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkwithinfo_t"))))


type 't var =
(FStar_Ident.lident, 't) withinfo_t


type sconst =
FStar_Const.sconst


type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string Prims.option


let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))


let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))


let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_34_23) -> begin
_34_23
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_34_26) -> begin
_34_26
end))


type 'a memo =
'a Prims.option FStar_ST.ref


type arg_qualifier =
| Implicit of Prims.bool
| Equality


let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))


let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))


let ___Implicit____0 = (fun projectee -> (match (projectee) with
| Implicit (_34_30) -> begin
_34_30
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
| U_zero (_) -> begin
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
| U_unknown (_) -> begin
true
end
| _ -> begin
false
end))


let ___U_succ____0 = (fun projectee -> (match (projectee) with
| U_succ (_34_33) -> begin
_34_33
end))


let ___U_max____0 = (fun projectee -> (match (projectee) with
| U_max (_34_36) -> begin
_34_36
end))


let ___U_bvar____0 = (fun projectee -> (match (projectee) with
| U_bvar (_34_39) -> begin
_34_39
end))


let ___U_name____0 = (fun projectee -> (match (projectee) with
| U_name (_34_42) -> begin
_34_42
end))


let ___U_unif____0 = (fun projectee -> (match (projectee) with
| U_unif (_34_45) -> begin
_34_45
end))


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


let is_Delta_constant = (fun _discr_ -> (match (_discr_) with
| Delta_constant (_) -> begin
true
end
| _ -> begin
false
end))


let is_Delta_defined_at_level = (fun _discr_ -> (match (_discr_) with
| Delta_defined_at_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Delta_equational = (fun _discr_ -> (match (_discr_) with
| Delta_equational (_) -> begin
true
end
| _ -> begin
false
end))


let is_Delta_abstract = (fun _discr_ -> (match (_discr_) with
| Delta_abstract (_) -> begin
true
end
| _ -> begin
false
end))


let ___Delta_defined_at_level____0 = (fun projectee -> (match (projectee) with
| Delta_defined_at_level (_34_48) -> begin
_34_48
end))


let ___Delta_abstract____0 = (fun projectee -> (match (projectee) with
| Delta_abstract (_34_51) -> begin
_34_51
end))


type term' =
| Tm_bvar of bv
| Tm_name of bv
| Tm_fvar of fv
| Tm_uinst of (term * universes)
| Tm_constant of sconst
| Tm_type of universe
| Tm_abs of (binders * term * (lcomp, residual_comp) FStar_Util.either Prims.option)
| Tm_arrow of (binders * comp)
| Tm_refine of (bv * term)
| Tm_app of (term * args)
| Tm_match of (term * branch Prims.list)
| Tm_ascribed of (term * (term, comp) FStar_Util.either * FStar_Ident.lident Prims.option)
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
{comp_univs : universes; effect_name : FStar_Ident.lident; result_typ : typ; effect_args : args; flags : cflags Prims.list} 
 and comp' =
| Total of (typ * universe Prims.option)
| GTotal of (typ * universe Prims.option)
| Comp of comp_typ 
 and cflags =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| LEMMA
| CPS
| DECREASES of term 
 and metadata =
| Meta_pattern of args Prims.list
| Meta_named of FStar_Ident.lident
| Meta_labeled of (Prims.string * FStar_Range.range * Prims.bool)
| Meta_desugared of meta_source_info
| Meta_monadic of (monad_name * typ)
| Meta_monadic_lift of (monad_name * monad_name * typ) 
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
| NT of (bv * term)
| UN of (Prims.int * universe)
| UD of (univ_name * Prims.int) 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : FStar_Range.range; vars : free_vars memo} 
 and bv =
{ppname : FStar_Ident.ident; index : Prims.int; sort : term} 
 and fv =
{fv_name : term var; fv_delta : delta_depth; fv_qual : fv_qual Prims.option} 
 and free_vars =
{free_names : bv FStar_Util.set; free_uvars : uvars; free_univs : universe_uvar FStar_Util.set; free_univ_names : univ_name FStar_Util.fifo_set} 
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
(bv, fv) FStar_Util.either 
 and letbindings =
(Prims.bool * letbinding Prims.list) 
 and subst_ts =
(subst_elt Prims.list Prims.list * FStar_Range.range Prims.option) 
 and freenames =
bv FStar_Util.set 
 and uvars =
(uvar * typ) FStar_Util.set 
 and residual_comp =
(FStar_Ident.lident * cflags Prims.list)


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
| Tm_unknown (_) -> begin
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


let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkletbinding"))))


let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkcomp_typ"))))


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
| TOTAL (_) -> begin
true
end
| _ -> begin
false
end))


let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT (_) -> begin
true
end
| _ -> begin
false
end))


let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN (_) -> begin
true
end
| _ -> begin
false
end))


let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN (_) -> begin
true
end
| _ -> begin
false
end))


let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL (_) -> begin
true
end
| _ -> begin
false
end))


let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA (_) -> begin
true
end
| _ -> begin
false
end))


let is_CPS = (fun _discr_ -> (match (_discr_) with
| CPS (_) -> begin
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


let is_Meta_monadic = (fun _discr_ -> (match (_discr_) with
| Meta_monadic (_) -> begin
true
end
| _ -> begin
false
end))


let is_Meta_monadic_lift = (fun _discr_ -> (match (_discr_) with
| Meta_monadic_lift (_) -> begin
true
end
| _ -> begin
false
end))


let is_Uvar = (fun _ _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Fixed = (fun _ _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop (_) -> begin
true
end
| _ -> begin
false
end))


let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mutable_alloc = (fun _discr_ -> (match (_discr_) with
| Mutable_alloc (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mutable_rval = (fun _discr_ -> (match (_discr_) with
| Mutable_rval (_) -> begin
true
end
| _ -> begin
false
end))


let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor (_) -> begin
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


let is_Mksyntax = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mksyntax"))))


let is_Mkbv : bv  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkbv"))))


let is_Mkfv : fv  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkfv"))))


let is_Mkfree_vars : free_vars  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkfree_vars"))))


let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mklcomp"))))


let ___Tm_bvar____0 = (fun projectee -> (match (projectee) with
| Tm_bvar (_34_85) -> begin
_34_85
end))


let ___Tm_name____0 = (fun projectee -> (match (projectee) with
| Tm_name (_34_88) -> begin
_34_88
end))


let ___Tm_fvar____0 = (fun projectee -> (match (projectee) with
| Tm_fvar (_34_91) -> begin
_34_91
end))


let ___Tm_uinst____0 = (fun projectee -> (match (projectee) with
| Tm_uinst (_34_94) -> begin
_34_94
end))


let ___Tm_constant____0 = (fun projectee -> (match (projectee) with
| Tm_constant (_34_97) -> begin
_34_97
end))


let ___Tm_type____0 = (fun projectee -> (match (projectee) with
| Tm_type (_34_100) -> begin
_34_100
end))


let ___Tm_abs____0 = (fun projectee -> (match (projectee) with
| Tm_abs (_34_103) -> begin
_34_103
end))


let ___Tm_arrow____0 = (fun projectee -> (match (projectee) with
| Tm_arrow (_34_106) -> begin
_34_106
end))


let ___Tm_refine____0 = (fun projectee -> (match (projectee) with
| Tm_refine (_34_109) -> begin
_34_109
end))


let ___Tm_app____0 = (fun projectee -> (match (projectee) with
| Tm_app (_34_112) -> begin
_34_112
end))


let ___Tm_match____0 = (fun projectee -> (match (projectee) with
| Tm_match (_34_115) -> begin
_34_115
end))


let ___Tm_ascribed____0 = (fun projectee -> (match (projectee) with
| Tm_ascribed (_34_118) -> begin
_34_118
end))


let ___Tm_let____0 = (fun projectee -> (match (projectee) with
| Tm_let (_34_121) -> begin
_34_121
end))


let ___Tm_uvar____0 = (fun projectee -> (match (projectee) with
| Tm_uvar (_34_124) -> begin
_34_124
end))


let ___Tm_delayed____0 = (fun projectee -> (match (projectee) with
| Tm_delayed (_34_127) -> begin
_34_127
end))


let ___Tm_meta____0 = (fun projectee -> (match (projectee) with
| Tm_meta (_34_130) -> begin
_34_130
end))


let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_34_133) -> begin
_34_133
end))


let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_34_136) -> begin
_34_136
end))


let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_34_139) -> begin
_34_139
end))


let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_34_142) -> begin
_34_142
end))


let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_34_145) -> begin
_34_145
end))


let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_34_148) -> begin
_34_148
end))


let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_34_153) -> begin
_34_153
end))


let ___GTotal____0 = (fun projectee -> (match (projectee) with
| GTotal (_34_156) -> begin
_34_156
end))


let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_34_159) -> begin
_34_159
end))


let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_34_162) -> begin
_34_162
end))


let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_34_165) -> begin
_34_165
end))


let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_34_168) -> begin
_34_168
end))


let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_34_171) -> begin
_34_171
end))


let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_34_174) -> begin
_34_174
end))


let ___Meta_monadic____0 = (fun projectee -> (match (projectee) with
| Meta_monadic (_34_177) -> begin
_34_177
end))


let ___Meta_monadic_lift____0 = (fun projectee -> (match (projectee) with
| Meta_monadic_lift (_34_180) -> begin
_34_180
end))


let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_34_183) -> begin
_34_183
end))


let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_34_186) -> begin
_34_186
end))


let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_34_189) -> begin
_34_189
end))


let ___DB____0 = (fun projectee -> (match (projectee) with
| DB (_34_192) -> begin
_34_192
end))


let ___NM____0 = (fun projectee -> (match (projectee) with
| NM (_34_195) -> begin
_34_195
end))


let ___NT____0 = (fun projectee -> (match (projectee) with
| NT (_34_198) -> begin
_34_198
end))


let ___UN____0 = (fun projectee -> (match (projectee) with
| UN (_34_201) -> begin
_34_201
end))


let ___UD____0 = (fun projectee -> (match (projectee) with
| UD (_34_204) -> begin
_34_204
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


let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))


let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))


let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unfold_for_unification_and_vcgen = (fun _discr_ -> (match (_discr_) with
| Unfold_for_unification_and_vcgen (_) -> begin
true
end
| _ -> begin
false
end))


let is_Visible_default = (fun _discr_ -> (match (_discr_) with
| Visible_default (_) -> begin
true
end
| _ -> begin
false
end))


let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inline_for_extraction = (fun _discr_ -> (match (_discr_) with
| Inline_for_extraction (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoExtract = (fun _discr_ -> (match (_discr_) with
| NoExtract (_) -> begin
true
end
| _ -> begin
false
end))


let is_Noeq = (fun _discr_ -> (match (_discr_) with
| Noeq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unopteq = (fun _discr_ -> (match (_discr_) with
| Unopteq (_) -> begin
true
end
| _ -> begin
false
end))


let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reifiable = (fun _discr_ -> (match (_discr_) with
| Reifiable (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reflectable = (fun _discr_ -> (match (_discr_) with
| Reflectable (_) -> begin
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


let is_Action = (fun _discr_ -> (match (_discr_) with
| Action (_) -> begin
true
end
| _ -> begin
false
end))


let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor (_) -> begin
true
end
| _ -> begin
false
end))


let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))


let is_OnlyName = (fun _discr_ -> (match (_discr_) with
| OnlyName (_) -> begin
true
end
| _ -> begin
false
end))


let ___Reflectable____0 = (fun projectee -> (match (projectee) with
| Reflectable (_34_212) -> begin
_34_212
end))


let ___Discriminator____0 = (fun projectee -> (match (projectee) with
| Discriminator (_34_215) -> begin
_34_215
end))


let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_34_218) -> begin
_34_218
end))


let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_34_221) -> begin
_34_221
end))


let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_34_224) -> begin
_34_224
end))


let ___Action____0 = (fun projectee -> (match (projectee) with
| Action (_34_227) -> begin
_34_227
end))


type attribute =
term


type tycon =
(FStar_Ident.lident * binders * typ)


type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}


let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkmonad_abbrev"))))


type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift_wp : tscheme Prims.option; lift : tscheme Prims.option}


let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mksub_eff"))))


type action =
{action_name : FStar_Ident.lident; action_unqualified_name : FStar_Ident.ident; action_univs : univ_names; action_defn : term; action_typ : typ}


let is_Mkaction : action  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkaction"))))


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


let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkeff_decl"))))


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


let is_Sig_new_effect_for_free = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect_for_free (_) -> begin
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
| Sig_inductive_typ (_34_266) -> begin
_34_266
end))


let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_34_269) -> begin
_34_269
end))


let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_34_272) -> begin
_34_272
end))


let ___Sig_declare_typ____0 = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_34_275) -> begin
_34_275
end))


let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_34_278) -> begin
_34_278
end))


let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_34_281) -> begin
_34_281
end))


let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_34_284) -> begin
_34_284
end))


let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_34_287) -> begin
_34_287
end))


let ___Sig_new_effect_for_free____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect_for_free (_34_290) -> begin
_34_290
end))


let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_34_293) -> begin
_34_293
end))


let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_34_296) -> begin
_34_296
end))


let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_34_299) -> begin
_34_299
end))


type sigelts =
sigelt Prims.list


type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}


let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkmodul"))))


type path =
Prims.string Prims.list


type subst_t =
subst_elt Prims.list


type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax


type mk_t =
(term', term') mk_t_a


let contains_reflectable : qualifier Prims.list  ->  Prims.bool = (fun l -> (FStar_Util.for_some (fun _34_1 -> (match (_34_1) with
| Reflectable (_34_316) -> begin
true
end
| _34_319 -> begin
false
end)) l))


let withinfo = (fun v s r -> {v = v; ty = s; p = r})


let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))


let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))


let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (

let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = (Prims.parse_int "0")) then begin
(x.index - y.index)
end else begin
i
end))


let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.fv_name.v)
end))


let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)


let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (

let _34_338 = x
in {ppname = (FStar_Ident.mk_ident ((x.ppname.FStar_Ident.idText), (r))); index = _34_338.index; sort = _34_338.sort}))


let syn = (fun p k f -> (f k p))


let mk_fvs = (fun _34_343 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))


let mk_uvs = (fun _34_344 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))


let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun _34_345 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))


let new_uv_set : Prims.unit  ->  uvars = (fun _34_347 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _34_355 _34_359 -> (match (((_34_355), (_34_359))) with
| ((x, _34_354), (y, _34_358)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _34_351 -> (match (_34_351) with
| (x, _34_350) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))


let new_universe_uvar_set : Prims.unit  ->  universe_uvar FStar_Util.set = (fun _34_360 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))


let new_universe_names_fifo_set : Prims.unit  ->  univ_name FStar_Util.fifo_set = (fun _34_364 -> (match (()) with
| () -> begin
(FStar_Util.new_fifo_set (fun x y -> (FStar_String.compare (FStar_Ident.text_of_id x) (FStar_Ident.text_of_id y))) (fun x -> (FStar_Util.hashcode (FStar_Ident.text_of_id x))))
end))


let no_names : bv FStar_Util.set = (new_bv_set ())


let no_uvs : uvars = (new_uv_set ())


let no_universe_uvars : universe_uvar FStar_Util.set = (new_universe_uvar_set ())


let no_universe_names : univ_name FStar_Util.fifo_set = (new_universe_names_fifo_set ())


let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars; free_univ_names = no_universe_names}


let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))


let memo_no_names : bv FStar_Util.set Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))


let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))


let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))


let mk = (fun t topt r -> (let _133_1323 = (FStar_Util.mk_ref topt)
in (let _133_1322 = (FStar_Util.mk_ref None)
in {n = t; tk = _133_1323; pos = r; vars = _133_1322})))


let bv_to_tm : bv  ->  term = (fun bv -> (let _133_1326 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (Some (bv.sort.n)) _133_1326)))


let bv_to_name : bv  ->  term = (fun bv -> (let _133_1329 = (range_of_bv bv)
in (mk (Tm_name (bv)) (Some (bv.sort.n)) _133_1329)))


let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _34_383 -> begin
(mk (Tm_app (((t1), (args)))) k p)
end))


let mk_Tm_uinst : term  ->  universes  ->  term = (fun t _34_2 -> (match (_34_2) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_34_389) -> begin
(mk (Tm_uinst (((t), (us)))) None t.pos)
end
| _34_392 -> begin
(failwith "Unexpected universe instantiation")
end)
end))


let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _34_402 -> begin
(mk_Tm_app t args' kopt r)
end))


let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))


let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  term = (fun lr pos -> (let _133_1364 = (let _133_1363 = (let _133_1362 = (FStar_Util.mk_ref None)
in ((lr), (_133_1362)))
in Tm_delayed (_133_1363))
in (mk _133_1364 None pos)))


let mk_Total' : typ  ->  universe Prims.option  ->  comp = (fun t u -> (mk (Total (((t), (u)))) None t.pos))


let mk_GTotal' : typ  ->  universe Prims.option  ->  comp = (fun t u -> (mk (GTotal (((t), (u)))) None t.pos))


let mk_Total : typ  ->  comp = (fun t -> (mk_Total' t None))


let mk_GTotal : typ  ->  comp = (fun t -> (mk_GTotal' t None))


let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))


let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun _34_421 -> (match (_34_421) with
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
| _34_430 -> begin
false
end))


let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (_34_433) -> begin
true
end
| _34_436 -> begin
false
end))


let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident (("_"), (FStar_Range.dummyRange)))


let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = (Prims.parse_int "0"); sort = k})


let mk_binder : bv  ->  binder = (fun a -> ((a), (None)))


let null_binder : term  ->  binder = (fun t -> (let _133_1399 = (null_bv t)
in ((_133_1399), (None))))


let imp_tag : arg_qualifier = Implicit (false)


let iarg : term  ->  arg = (fun t -> ((t), (Some (imp_tag))))


let as_arg : term  ->  arg = (fun t -> ((t), (None)))


let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))


let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))


let is_top_level : letbinding Prims.list  ->  Prims.bool = (fun _34_3 -> (match (_34_3) with
| ({lbname = FStar_Util.Inr (_34_456); lbunivs = _34_454; lbtyp = _34_452; lbeff = _34_450; lbdef = _34_448})::_34_446 -> begin
true
end
| _34_461 -> begin
false
end))


let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun _34_466 out -> (match (_34_466) with
| (x, _34_465) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))


let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> ((t), (None))))))


let binders_of_freenames : freenames  ->  binders = (fun fvs -> (let _133_1419 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _133_1419 binders_of_list)))


let is_implicit : aqual  ->  Prims.bool = (fun _34_4 -> (match (_34_4) with
| Some (Implicit (_34_473)) -> begin
true
end
| _34_477 -> begin
false
end))


let as_implicit : Prims.bool  ->  aqual = (fun _34_5 -> (match (_34_5) with
| true -> begin
Some (imp_tag)
end
| _34_481 -> begin
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
| Pat_cons (_34_496, pats) -> begin
(FStar_List.fold_left (fun b _34_504 -> (match (_34_504) with
| (p, _34_503) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj ((p)::_34_506) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(failwith "impossible")
end))
in (let _133_1432 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev _133_1432))))


let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (

let x = (FStar_ST.alloc (Prims.parse_int "0"))
in (

let gen = (fun _34_514 -> (match (()) with
| () -> begin
(

let _34_515 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (

let reset = (fun _34_518 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x (Prims.parse_int "0"))
end))
in ((gen), (reset)))))


let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)


let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)


let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun _34_6 -> (match (_34_6) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))


let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (

let id = (FStar_Ident.mk_ident ((s), ((range_of_ropt r))))
in (let _133_1457 = (next_id ())
in {ppname = id; index = _133_1457; sort = t})))


let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv FStar_Ident.reserved_prefix ropt t))


let freshen_bv : bv  ->  bv = (fun bv -> if (is_null_bv bv) then begin
(let _133_1465 = (let _133_1464 = (range_of_bv bv)
in Some (_133_1464))
in (new_bv _133_1465 bv.sort))
end else begin
(

let _34_530 = bv
in (let _133_1466 = (next_id ())
in {ppname = _34_530.ppname; index = _133_1466; sort = _34_530.sort}))
end)


let new_univ_name : FStar_Range.range Prims.option  ->  univ_name = (fun ropt -> (

let id = (next_id ())
in (let _133_1471 = (let _133_1470 = (let _133_1469 = (FStar_Util.string_of_int id)
in (Prims.strcat "\'uu___" _133_1469))
in ((_133_1470), ((range_of_ropt ropt))))
in (FStar_Ident.mk_ident _133_1471))))


let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})


let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match (((l1), (l2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _34_550 -> begin
false
end))


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.fv_name.v fv2.fv_name.v))


let fv_eq_lid : fv  ->  FStar_Ident.lident  ->  Prims.bool = (fun fv lid -> (FStar_Ident.lid_equals fv.fv_name.v lid))


let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (

let _34_557 = bv
in {ppname = (FStar_Ident.mk_ident ((bv.ppname.FStar_Ident.idText), (r))); index = _34_557.index; sort = _34_557.sort}))


let lid_as_fv : FStar_Ident.lident  ->  delta_depth  ->  fv_qual Prims.option  ->  fv = (fun l dd dq -> (let _133_1500 = (withinfo l tun (FStar_Ident.range_of_lid l))
in {fv_name = _133_1500; fv_delta = dd; fv_qual = dq}))


let fv_to_tm : fv  ->  term = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid fv.fv_name.v)))


let fvar : FStar_Ident.lident  ->  delta_depth  ->  fv_qual Prims.option  ->  term = (fun l dd dq -> (let _133_1509 = (lid_as_fv l dd dq)
in (fv_to_tm _133_1509)))


let lid_of_fv : fv  ->  FStar_Ident.lid = (fun fv -> fv.fv_name.v)


let range_of_fv : fv  ->  FStar_Range.range = (fun fv -> (let _133_1514 = (lid_of_fv fv)
in (FStar_Ident.range_of_lid _133_1514)))


let has_simple_attribute : term Prims.list  ->  Prims.string  ->  Prims.bool = (fun l s -> (FStar_List.existsb (fun _34_7 -> (match (_34_7) with
| {n = Tm_constant (FStar_Const.Const_string (data, _34_579)); tk = _34_576; pos = _34_574; vars = _34_572} when ((FStar_Util.string_of_unicode data) = s) -> begin
true
end
| _34_585 -> begin
false
end)) l))




