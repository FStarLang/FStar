
open Prims

type ident =
FStar_Ident.ident


type lident =
FStar_Ident.lid


type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}


let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkwithinfo_t"))))


type 't var =
(lident, 't) withinfo_t


type fieldname =
lident


type 'a bvdef =
{ppname : ident; realname : ident}


let is_Mkbvdef = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkbvdef"))))


type ('a, 't) bvar =
('a bvdef, 't) withinfo_t


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
| SetOptions (_30_21) -> begin
_30_21
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_30_24) -> begin
_30_24
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
| Implicit (_30_28) -> begin
_30_28
end))


type aqual =
arg_qualifier Prims.option


type typ' =
| Typ_btvar of btvar
| Typ_const of ftvar
| Typ_fun of (binders * comp)
| Typ_refine of (bvvar * typ)
| Typ_app of (typ * args)
| Typ_lam of (binders * typ)
| Typ_ascribed of (typ * knd)
| Typ_meta of meta_t
| Typ_uvar of (uvar_t * knd)
| Typ_delayed of (((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either * typ memo)
| Typ_unknown 
 and comp_typ =
{effect_name : lident; result_typ : typ; effect_args : args; flags : cflags Prims.list} 
 and comp' =
| Total of typ
| Comp of comp_typ 
 and cflags =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| LEMMA
| DECREASES of exp 
 and meta_t =
| Meta_pattern of (typ * arg Prims.list Prims.list)
| Meta_named of (typ * lident)
| Meta_labeled of (typ * Prims.string * FStar_Range.range * Prims.bool)
| Meta_refresh_label of (typ * Prims.bool Prims.option * FStar_Range.range)
| Meta_slack_formula of (typ * typ * Prims.bool FStar_ST.ref) 
 and 'a uvar_basis =
| Uvar
| Fixed of 'a 
 and exp' =
| Exp_bvar of bvvar
| Exp_fvar of (fvvar * fv_qual Prims.option)
| Exp_constant of sconst
| Exp_abs of (binders * exp)
| Exp_app of (exp * args)
| Exp_match of (exp * (pat * exp Prims.option * exp) Prims.list)
| Exp_ascribed of (exp * typ * lident Prims.option)
| Exp_let of (letbindings * exp)
| Exp_uvar of (uvar_e * typ)
| Exp_delayed of (exp * subst_t * exp memo)
| Exp_meta of meta_e 
 and meta_e =
| Meta_desugared of (exp * meta_source_info) 
 and meta_source_info =
| Data_app
| Sequence
| Primop
| Masked_effect
| Meta_smt_pat 
 and fv_qual =
| Data_ctor
| Record_projector of lident
| Record_ctor of (lident * fieldname Prims.list) 
 and pat' =
| Pat_disj of pat Prims.list
| Pat_constant of sconst
| Pat_cons of (fvvar * fv_qual Prims.option * (pat * Prims.bool) Prims.list)
| Pat_var of bvvar
| Pat_tvar of btvar
| Pat_wild of bvvar
| Pat_twild of btvar
| Pat_dot_term of (bvvar * exp)
| Pat_dot_typ of (btvar * typ) 
 and knd' =
| Kind_type
| Kind_effect
| Kind_abbrev of (kabbrev * knd)
| Kind_arrow of (binders * knd)
| Kind_uvar of uvar_k_app
| Kind_lam of (binders * knd)
| Kind_delayed of (knd * subst_t * knd memo)
| Kind_unknown 
 and letbinding =
{lbname : lbname; lbtyp : typ; lbeff : lident; lbdef : exp} 
 and freevars =
{ftvs : btvar FStar_Util.set; fxvs : bvvar FStar_Util.set} 
 and uvars =
{uvars_k : uvar_k FStar_Util.set; uvars_t : (uvar_t * knd) FStar_Util.set; uvars_e : (uvar_e * typ) FStar_Util.set} 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : FStar_Range.range; fvs : freevars memo; uvs : uvars memo} 
 and arg =
((typ, exp) FStar_Util.either * aqual) 
 and args =
arg Prims.list 
 and binder =
((btvar, bvvar) FStar_Util.either * arg_qualifier Prims.option) 
 and binders =
binder Prims.list 
 and typ =
(typ', knd) syntax 
 and comp =
(comp', Prims.unit) syntax 
 and uvar_t =
typ uvar_basis FStar_Unionfind.uvar 
 and exp =
(exp', typ) syntax 
 and uvar_e =
exp uvar_basis FStar_Unionfind.uvar 
 and btvdef =
typ bvdef 
 and bvvdef =
exp bvdef 
 and pat =
(pat', (knd, typ) FStar_Util.either Prims.option) withinfo_t 
 and knd =
(knd', Prims.unit) syntax 
 and uvar_k_app =
(uvar_k * args) 
 and kabbrev =
(lident * args) 
 and uvar_k =
knd uvar_basis FStar_Unionfind.uvar 
 and lbname =
(bvvdef, lident) FStar_Util.either 
 and letbindings =
(Prims.bool * letbinding Prims.list) 
 and subst_t =
subst_elt Prims.list Prims.list 
 and subst_map =
(typ, exp) FStar_Util.either FStar_Util.smap 
 and subst_elt =
((btvdef * typ), (bvvdef * exp)) FStar_Util.either 
 and fvar =
(btvdef, bvvdef) FStar_Util.either 
 and btvar =
(typ, knd) bvar 
 and bvvar =
(exp, typ) bvar 
 and ftvar =
knd var 
 and fvvar =
typ var


let is_Typ_btvar = (fun _discr_ -> (match (_discr_) with
| Typ_btvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_const = (fun _discr_ -> (match (_discr_) with
| Typ_const (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_fun = (fun _discr_ -> (match (_discr_) with
| Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_refine = (fun _discr_ -> (match (_discr_) with
| Typ_refine (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_app = (fun _discr_ -> (match (_discr_) with
| Typ_app (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_lam = (fun _discr_ -> (match (_discr_) with
| Typ_lam (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_ascribed = (fun _discr_ -> (match (_discr_) with
| Typ_ascribed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_meta = (fun _discr_ -> (match (_discr_) with
| Typ_meta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_uvar = (fun _discr_ -> (match (_discr_) with
| Typ_uvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_delayed = (fun _discr_ -> (match (_discr_) with
| Typ_delayed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Typ_unknown = (fun _discr_ -> (match (_discr_) with
| Typ_unknown (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkcomp_typ"))))


let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
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


let is_Meta_refresh_label = (fun _discr_ -> (match (_discr_) with
| Meta_refresh_label (_) -> begin
true
end
| _ -> begin
false
end))


let is_Meta_slack_formula = (fun _discr_ -> (match (_discr_) with
| Meta_slack_formula (_) -> begin
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


let is_Exp_bvar = (fun _discr_ -> (match (_discr_) with
| Exp_bvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_fvar = (fun _discr_ -> (match (_discr_) with
| Exp_fvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_constant = (fun _discr_ -> (match (_discr_) with
| Exp_constant (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_abs = (fun _discr_ -> (match (_discr_) with
| Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_app = (fun _discr_ -> (match (_discr_) with
| Exp_app (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_match = (fun _discr_ -> (match (_discr_) with
| Exp_match (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_ascribed = (fun _discr_ -> (match (_discr_) with
| Exp_ascribed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_let = (fun _discr_ -> (match (_discr_) with
| Exp_let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_uvar = (fun _discr_ -> (match (_discr_) with
| Exp_uvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_delayed = (fun _discr_ -> (match (_discr_) with
| Exp_delayed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exp_meta = (fun _discr_ -> (match (_discr_) with
| Exp_meta (_) -> begin
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


let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
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


let is_Pat_tvar = (fun _discr_ -> (match (_discr_) with
| Pat_tvar (_) -> begin
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


let is_Pat_twild = (fun _discr_ -> (match (_discr_) with
| Pat_twild (_) -> begin
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


let is_Pat_dot_typ = (fun _discr_ -> (match (_discr_) with
| Pat_dot_typ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_type = (fun _discr_ -> (match (_discr_) with
| Kind_type (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_effect = (fun _discr_ -> (match (_discr_) with
| Kind_effect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_abbrev = (fun _discr_ -> (match (_discr_) with
| Kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_arrow = (fun _discr_ -> (match (_discr_) with
| Kind_arrow (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_uvar = (fun _discr_ -> (match (_discr_) with
| Kind_uvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_lam = (fun _discr_ -> (match (_discr_) with
| Kind_lam (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_delayed = (fun _discr_ -> (match (_discr_) with
| Kind_delayed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_unknown = (fun _discr_ -> (match (_discr_) with
| Kind_unknown (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkletbinding"))))


let is_Mkfreevars : freevars  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkfreevars"))))


let is_Mkuvars : uvars  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkuvars"))))


let is_Mksyntax = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mksyntax"))))


let ___Typ_btvar____0 = (fun projectee -> (match (projectee) with
| Typ_btvar (_30_52) -> begin
_30_52
end))


let ___Typ_const____0 = (fun projectee -> (match (projectee) with
| Typ_const (_30_55) -> begin
_30_55
end))


let ___Typ_fun____0 = (fun projectee -> (match (projectee) with
| Typ_fun (_30_58) -> begin
_30_58
end))


let ___Typ_refine____0 = (fun projectee -> (match (projectee) with
| Typ_refine (_30_61) -> begin
_30_61
end))


let ___Typ_app____0 = (fun projectee -> (match (projectee) with
| Typ_app (_30_64) -> begin
_30_64
end))


let ___Typ_lam____0 = (fun projectee -> (match (projectee) with
| Typ_lam (_30_67) -> begin
_30_67
end))


let ___Typ_ascribed____0 = (fun projectee -> (match (projectee) with
| Typ_ascribed (_30_70) -> begin
_30_70
end))


let ___Typ_meta____0 = (fun projectee -> (match (projectee) with
| Typ_meta (_30_73) -> begin
_30_73
end))


let ___Typ_uvar____0 = (fun projectee -> (match (projectee) with
| Typ_uvar (_30_76) -> begin
_30_76
end))


let ___Typ_delayed____0 = (fun projectee -> (match (projectee) with
| Typ_delayed (_30_79) -> begin
_30_79
end))


let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_30_83) -> begin
_30_83
end))


let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_30_86) -> begin
_30_86
end))


let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_30_89) -> begin
_30_89
end))


let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_30_92) -> begin
_30_92
end))


let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_30_95) -> begin
_30_95
end))


let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_30_98) -> begin
_30_98
end))


let ___Meta_refresh_label____0 = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_30_101) -> begin
_30_101
end))


let ___Meta_slack_formula____0 = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_30_104) -> begin
_30_104
end))


let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_30_107) -> begin
_30_107
end))


let ___Exp_bvar____0 = (fun projectee -> (match (projectee) with
| Exp_bvar (_30_110) -> begin
_30_110
end))


let ___Exp_fvar____0 = (fun projectee -> (match (projectee) with
| Exp_fvar (_30_113) -> begin
_30_113
end))


let ___Exp_constant____0 = (fun projectee -> (match (projectee) with
| Exp_constant (_30_116) -> begin
_30_116
end))


let ___Exp_abs____0 = (fun projectee -> (match (projectee) with
| Exp_abs (_30_119) -> begin
_30_119
end))


let ___Exp_app____0 = (fun projectee -> (match (projectee) with
| Exp_app (_30_122) -> begin
_30_122
end))


let ___Exp_match____0 = (fun projectee -> (match (projectee) with
| Exp_match (_30_125) -> begin
_30_125
end))


let ___Exp_ascribed____0 = (fun projectee -> (match (projectee) with
| Exp_ascribed (_30_128) -> begin
_30_128
end))


let ___Exp_let____0 = (fun projectee -> (match (projectee) with
| Exp_let (_30_131) -> begin
_30_131
end))


let ___Exp_uvar____0 = (fun projectee -> (match (projectee) with
| Exp_uvar (_30_134) -> begin
_30_134
end))


let ___Exp_delayed____0 = (fun projectee -> (match (projectee) with
| Exp_delayed (_30_137) -> begin
_30_137
end))


let ___Exp_meta____0 = (fun projectee -> (match (projectee) with
| Exp_meta (_30_140) -> begin
_30_140
end))


let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_30_142) -> begin
_30_142
end))


let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_30_145) -> begin
_30_145
end))


let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_30_148) -> begin
_30_148
end))


let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_30_151) -> begin
_30_151
end))


let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_30_154) -> begin
_30_154
end))


let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_30_157) -> begin
_30_157
end))


let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_30_160) -> begin
_30_160
end))


let ___Pat_tvar____0 = (fun projectee -> (match (projectee) with
| Pat_tvar (_30_163) -> begin
_30_163
end))


let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_30_166) -> begin
_30_166
end))


let ___Pat_twild____0 = (fun projectee -> (match (projectee) with
| Pat_twild (_30_169) -> begin
_30_169
end))


let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_30_172) -> begin
_30_172
end))


let ___Pat_dot_typ____0 = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_30_175) -> begin
_30_175
end))


let ___Kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Kind_abbrev (_30_178) -> begin
_30_178
end))


let ___Kind_arrow____0 = (fun projectee -> (match (projectee) with
| Kind_arrow (_30_181) -> begin
_30_181
end))


let ___Kind_uvar____0 = (fun projectee -> (match (projectee) with
| Kind_uvar (_30_184) -> begin
_30_184
end))


let ___Kind_lam____0 = (fun projectee -> (match (projectee) with
| Kind_lam (_30_187) -> begin
_30_187
end))


let ___Kind_delayed____0 = (fun projectee -> (match (projectee) with
| Kind_delayed (_30_190) -> begin
_30_190
end))


type subst =
subst_elt Prims.list


type either_var =
(btvar, bvvar) FStar_Util.either


type freevars_l =
either_var Prims.list


type formula =
typ


type formulae =
typ Prims.list


type qualifier =
| Private
| Assumption
| Opaque
| Logic
| Abstract
| New
| Discriminator of lident
| Projector of (lident * (btvdef, bvvdef) FStar_Util.either)
| RecordType of fieldname Prims.list
| RecordConstructor of fieldname Prims.list
| ExceptionConstructor
| DefaultEffect of lident Prims.option
| TotalEffect
| HasMaskedEffect
| Effect


let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))


let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque (_) -> begin
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


let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
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
| ExceptionConstructor (_) -> begin
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
| TotalEffect (_) -> begin
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


let ___Discriminator____0 = (fun projectee -> (match (projectee) with
| Discriminator (_30_197) -> begin
_30_197
end))


let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_30_200) -> begin
_30_200
end))


let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_30_203) -> begin
_30_203
end))


let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_30_206) -> begin
_30_206
end))


let ___DefaultEffect____0 = (fun projectee -> (match (projectee) with
| DefaultEffect (_30_209) -> begin
_30_209
end))


type tycon =
(lident * binders * knd)


type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}


let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkmonad_abbrev"))))


type sub_eff =
{source : lident; target : lident; lift : typ}


let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mksub_eff"))))


type eff_decl =
{mname : lident; binders : binders; qualifiers : qualifier Prims.list; signature : knd; ret : typ; bind_wp : typ; bind_wlp : typ; if_then_else : typ; ite_wp : typ; ite_wlp : typ; wp_binop : typ; wp_as_type : typ; close_wp : typ; close_wp_t : typ; assert_p : typ; assume_p : typ; null_wp : typ; trivial : typ} 
 and sigelt =
| Sig_tycon of (lident * binders * knd * lident Prims.list * lident Prims.list * qualifier Prims.list * FStar_Range.range)
| Sig_kind_abbrev of (lident * binders * knd * FStar_Range.range)
| Sig_typ_abbrev of (lident * binders * knd * typ * qualifier Prims.list * FStar_Range.range)
| Sig_datacon of (lident * typ * tycon * qualifier Prims.list * lident Prims.list * FStar_Range.range)
| Sig_val_decl of (lident * typ * qualifier Prims.list * FStar_Range.range)
| Sig_assume of (lident * formula * qualifier Prims.list * FStar_Range.range)
| Sig_let of (letbindings * FStar_Range.range * lident Prims.list * qualifier Prims.list)
| Sig_main of (exp * FStar_Range.range)
| Sig_bundle of (sigelt Prims.list * qualifier Prims.list * lident Prims.list * FStar_Range.range)
| Sig_new_effect of (eff_decl * FStar_Range.range)
| Sig_sub_effect of (sub_eff * FStar_Range.range)
| Sig_effect_abbrev of (lident * binders * comp * qualifier Prims.list * FStar_Range.range)
| Sig_pragma of (pragma * FStar_Range.range)


let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkeff_decl"))))


let is_Sig_tycon = (fun _discr_ -> (match (_discr_) with
| Sig_tycon (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sig_kind_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sig_typ_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_typ_abbrev (_) -> begin
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


let is_Sig_val_decl = (fun _discr_ -> (match (_discr_) with
| Sig_val_decl (_) -> begin
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


let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
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


let ___Sig_tycon____0 = (fun projectee -> (match (projectee) with
| Sig_tycon (_30_239) -> begin
_30_239
end))


let ___Sig_kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_30_242) -> begin
_30_242
end))


let ___Sig_typ_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_30_245) -> begin
_30_245
end))


let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_30_248) -> begin
_30_248
end))


let ___Sig_val_decl____0 = (fun projectee -> (match (projectee) with
| Sig_val_decl (_30_251) -> begin
_30_251
end))


let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_30_254) -> begin
_30_254
end))


let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_30_257) -> begin
_30_257
end))


let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_30_260) -> begin
_30_260
end))


let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_30_263) -> begin
_30_263
end))


let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_30_266) -> begin
_30_266
end))


let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_30_269) -> begin
_30_269
end))


let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_30_272) -> begin
_30_272
end))


let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_30_275) -> begin
_30_275
end))


type sigelts =
sigelt Prims.list


type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}


let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkmodul"))))


type ktec =
| K of knd
| T of (typ * knd Prims.option)
| E of exp
| C of comp


let is_K = (fun _discr_ -> (match (_discr_) with
| K (_) -> begin
true
end
| _ -> begin
false
end))


let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))


let is_E = (fun _discr_ -> (match (_discr_) with
| E (_) -> begin
true
end
| _ -> begin
false
end))


let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))


let ___K____0 = (fun projectee -> (match (projectee) with
| K (_30_284) -> begin
_30_284
end))


let ___T____0 = (fun projectee -> (match (projectee) with
| T (_30_287) -> begin
_30_287
end))


let ___E____0 = (fun projectee -> (match (projectee) with
| E (_30_290) -> begin
_30_290
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_30_293) -> begin
_30_293
end))


type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}


let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mklcomp"))))


type path =
Prims.string Prims.list


let dummyRange : FStar_Range.range = FStar_Range.dummyRange


let withinfo = (fun v s r -> {v = v; sort = s; p = r})


let withsort = (fun v s -> (withinfo v s dummyRange))


let mk_ident : (Prims.string * FStar_Range.range)  ->  ident = (fun _30_329 -> (match (_30_329) with
| (text, range) -> begin
{FStar_Ident.idText = text; FStar_Ident.idRange = range}
end))


let id_of_text : Prims.string  ->  ident = (fun str -> (mk_ident ((str), (dummyRange))))


let text_of_id : ident  ->  Prims.string = (fun id -> id.FStar_Ident.idText)


let text_of_path : path  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))


let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))


let path_of_lid : lident  ->  path = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))


let ids_of_lid : lident  ->  ident Prims.list = (fun lid -> (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))


let lid_of_ids : ident Prims.list  ->  lident = (fun ids -> (

let _30_340 = (FStar_Util.prefix ids)
in (match (_30_340) with
| (ns, id) -> begin
(

let nsstr = (let _131_1270 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _131_1270 text_of_path))
in {FStar_Ident.ns = ns; FStar_Ident.ident = id; FStar_Ident.nsstr = nsstr; FStar_Ident.str = if (nsstr = "") then begin
id.FStar_Ident.idText
end else begin
(Prims.strcat nsstr (Prims.strcat "." id.FStar_Ident.idText))
end})
end)))


let lid_of_path : path  ->  FStar_Range.range  ->  lident = (fun path pos -> (

let ids = (FStar_List.map (fun s -> (mk_ident ((s), (pos)))) path)
in (lid_of_ids ids)))


let text_of_lid : lident  ->  Prims.string = (fun lid -> lid.FStar_Ident.str)


let lid_equals : lident  ->  lident  ->  Prims.bool = (fun l1 l2 -> (l1.FStar_Ident.str = l2.FStar_Ident.str))


let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.FStar_Ident.idText = bvd2.realname.FStar_Ident.idText))


let order_bvd = (fun x y -> (match (((x), (y))) with
| (FStar_Util.Inl (_30_355), FStar_Util.Inr (_30_358)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Util.Inr (_30_362), FStar_Util.Inl (_30_365)) -> begin
(Prims.parse_int "1")
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end))


let lid_with_range : lident  ->  FStar_Range.range  ->  lident = (fun lid r -> (

let id = (

let _30_380 = lid.FStar_Ident.ident
in {FStar_Ident.idText = _30_380.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let _30_383 = lid
in {FStar_Ident.ns = _30_383.FStar_Ident.ns; FStar_Ident.ident = id; FStar_Ident.nsstr = _30_383.FStar_Ident.nsstr; FStar_Ident.str = _30_383.FStar_Ident.str})))


let range_of_lid : lident  ->  FStar_Range.range = (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idRange)


let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))


let syn = (fun p k f -> (f k p))


let mk_fvs = (fun _30_394 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))


let mk_uvs = (fun _30_395 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))


let new_ftv_set = (fun _30_396 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.FStar_Ident.idText y.v.realname.FStar_Ident.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.FStar_Ident.idText)))
end))


let new_uv_set = (fun _30_400 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))


let new_uvt_set = (fun _30_403 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _30_411 _30_415 -> (match (((_30_411), (_30_415))) with
| ((x, _30_410), (y, _30_414)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _30_407 -> (match (_30_407) with
| (x, _30_406) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))


let no_fvs : freevars = (let _131_1319 = (new_ftv_set ())
in (let _131_1318 = (new_ftv_set ())
in {ftvs = _131_1319; fxvs = _131_1318}))


let no_uvs : uvars = (let _131_1322 = (new_uv_set ())
in (let _131_1321 = (new_uvt_set ())
in (let _131_1320 = (new_uvt_set ())
in {uvars_k = _131_1322; uvars_t = _131_1321; uvars_e = _131_1320})))


let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))


let memo_no_fvs : freevars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_fvs)))


let freevars_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  freevars = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _30_1 -> (match (_30_1) with
| FStar_Util.Inl (btv) -> begin
(

let _30_421 = out
in (let _131_1327 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _131_1327; fxvs = _30_421.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(

let _30_425 = out
in (let _131_1328 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _30_425.ftvs; fxvs = _131_1328}))
end)) no_fvs)))


let list_of_freevars : freevars  ->  (btvar, bvvar) FStar_Util.either Prims.list = (fun fvs -> (let _131_1336 = (let _131_1332 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _131_1332 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _131_1335 = (let _131_1334 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _131_1334 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _131_1336 _131_1335))))


let get_unit_ref : Prims.unit  ->  Prims.unit Prims.option FStar_ST.ref = (fun _30_430 -> (match (()) with
| () -> begin
(

let x = (FStar_Util.mk_ref (Some (())))
in (

let _30_432 = (FStar_ST.op_Colon_Equals x None)
in x))
end))


let mk_Kind_type : (knd', Prims.unit) syntax = (let _131_1341 = (get_unit_ref ())
in (let _131_1340 = (mk_fvs ())
in (let _131_1339 = (mk_uvs ())
in {n = Kind_type; tk = _131_1341; pos = dummyRange; fvs = _131_1340; uvs = _131_1339})))


let mk_Kind_effect : (knd', Prims.unit) syntax = (let _131_1344 = (get_unit_ref ())
in (let _131_1343 = (mk_fvs ())
in (let _131_1342 = (mk_uvs ())
in {n = Kind_effect; tk = _131_1344; pos = dummyRange; fvs = _131_1343; uvs = _131_1342})))


let mk_Kind_abbrev : (kabbrev * knd)  ->  FStar_Range.range  ->  knd = (fun _30_436 p -> (match (_30_436) with
| (kabr, k) -> begin
(let _131_1351 = (get_unit_ref ())
in (let _131_1350 = (mk_fvs ())
in (let _131_1349 = (mk_uvs ())
in {n = Kind_abbrev (((kabr), (k))); tk = _131_1351; pos = p; fvs = _131_1350; uvs = _131_1349})))
end))


let mk_Kind_arrow : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _30_440 p -> (match (_30_440) with
| (bs, k) -> begin
(let _131_1358 = (get_unit_ref ())
in (let _131_1357 = (mk_fvs ())
in (let _131_1356 = (mk_uvs ())
in {n = Kind_arrow (((bs), (k))); tk = _131_1358; pos = p; fvs = _131_1357; uvs = _131_1356})))
end))


let mk_Kind_arrow' : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _30_444 p -> (match (_30_444) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _30_448 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow (((FStar_List.append bs bs')), (k')) p)
end
| _30_454 -> begin
(mk_Kind_arrow ((bs), (k)) p)
end)
end)
end))


let mk_Kind_uvar : uvar_k_app  ->  FStar_Range.range  ->  knd = (fun uv p -> (let _131_1369 = (get_unit_ref ())
in (let _131_1368 = (mk_fvs ())
in (let _131_1367 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _131_1369; pos = p; fvs = _131_1368; uvs = _131_1367}))))


let mk_Kind_lam : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _30_459 p -> (match (_30_459) with
| (vs, k) -> begin
(let _131_1376 = (get_unit_ref ())
in (let _131_1375 = (mk_fvs ())
in (let _131_1374 = (mk_uvs ())
in {n = Kind_lam (((vs), (k))); tk = _131_1376; pos = p; fvs = _131_1375; uvs = _131_1374})))
end))


let mk_Kind_delayed : (knd * subst_t * knd memo)  ->  FStar_Range.range  ->  knd = (fun _30_464 p -> (match (_30_464) with
| (k, s, m) -> begin
(let _131_1383 = (get_unit_ref ())
in (let _131_1382 = (mk_fvs ())
in (let _131_1381 = (mk_uvs ())
in {n = Kind_delayed (((k), (s), (m))); tk = _131_1383; pos = p; fvs = _131_1382; uvs = _131_1381})))
end))


let mk_Kind_unknown : (knd', Prims.unit) syntax = (let _131_1386 = (get_unit_ref ())
in (let _131_1385 = (mk_fvs ())
in (let _131_1384 = (mk_uvs ())
in {n = Kind_unknown; tk = _131_1386; pos = dummyRange; fvs = _131_1385; uvs = _131_1384})))


let get_knd_nref : Prims.unit  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun _30_466 -> (match (()) with
| () -> begin
(

let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (

let _30_468 = (FStar_ST.op_Colon_Equals x None)
in x))
end))


let get_knd_ref : (knd', Prims.unit) syntax Prims.option  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun k -> (

let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (

let _30_472 = (FStar_ST.op_Colon_Equals x k)
in x)))


let mk_Typ_btvar : btvar  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun x k p -> (let _131_1399 = (get_knd_ref k)
in (let _131_1398 = (mk_fvs ())
in (let _131_1397 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _131_1399; pos = p; fvs = _131_1398; uvs = _131_1397}))))


let mk_Typ_const : ftvar  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun x k p -> (let _131_1406 = (get_knd_ref k)
in {n = Typ_const (x); tk = _131_1406; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))


let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(failwith "Empty binders")
end
| _30_485 -> begin
Typ_fun (((bs), (c)))
end))


let mk_Typ_fun : (binders * comp)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_488 k p -> (match (_30_488) with
| (bs, c) -> begin
(let _131_1419 = (check_fun bs c p)
in (let _131_1418 = (FStar_Util.mk_ref k)
in (let _131_1417 = (mk_fvs ())
in (let _131_1416 = (mk_uvs ())
in {n = _131_1419; tk = _131_1418; pos = p; fvs = _131_1417; uvs = _131_1416}))))
end))


let mk_Typ_refine : (bvvar * formula)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_493 k p -> (match (_30_493) with
| (x, phi) -> begin
(let _131_1428 = (FStar_Util.mk_ref k)
in (let _131_1427 = (mk_fvs ())
in (let _131_1426 = (mk_uvs ())
in {n = Typ_refine (((x), (phi))); tk = _131_1428; pos = p; fvs = _131_1427; uvs = _131_1426})))
end))


let mk_Typ_app : (typ * args)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_498 k p -> (match (_30_498) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _30_503 -> begin
(let _131_1437 = (FStar_Util.mk_ref k)
in (let _131_1436 = (mk_fvs ())
in (let _131_1435 = (mk_uvs ())
in {n = Typ_app (((t1), (args))); tk = _131_1437; pos = p; fvs = _131_1436; uvs = _131_1435})))
end)
end))


let mk_Typ_app' : (typ * args)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_506 k p -> (match (_30_506) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _30_511 -> begin
(mk_Typ_app ((t1), (args)) k p)
end)
end))


let extend_typ_app : (typ * arg)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_514 k p -> (match (_30_514) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app ((h), ((FStar_List.append args ((arg)::[])))) k p)
end
| _30_522 -> begin
(mk_Typ_app ((t), ((arg)::[])) k p)
end)
end))


let mk_Typ_lam : (binders * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_525 k p -> (match (_30_525) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _30_530 -> begin
(let _131_1458 = (FStar_Util.mk_ref k)
in (let _131_1457 = (mk_fvs ())
in (let _131_1456 = (mk_uvs ())
in {n = Typ_lam (((b), (t))); tk = _131_1458; pos = p; fvs = _131_1457; uvs = _131_1456})))
end)
end))


let mk_Typ_lam' : (binders * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_533 k p -> (match (_30_533) with
| (bs, t) -> begin
(mk_Typ_lam ((bs), (t)) k p)
end))


let mk_Typ_ascribed' : (typ * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_538 k' p -> (match (_30_538) with
| (t, k) -> begin
(let _131_1473 = (FStar_Util.mk_ref k')
in (let _131_1472 = (mk_fvs ())
in (let _131_1471 = (mk_uvs ())
in {n = Typ_ascribed (((t), (k))); tk = _131_1473; pos = p; fvs = _131_1472; uvs = _131_1471})))
end))


let mk_Typ_ascribed : (typ * knd)  ->  FStar_Range.range  ->  typ = (fun _30_543 p -> (match (_30_543) with
| (t, k) -> begin
(mk_Typ_ascribed' ((t), (k)) (Some (k)) p)
end))


let mk_Typ_meta' : meta_t  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun m k p -> (let _131_1486 = (FStar_Util.mk_ref k)
in (let _131_1485 = (mk_fvs ())
in (let _131_1484 = (mk_uvs ())
in {n = Typ_meta (m); tk = _131_1486; pos = p; fvs = _131_1485; uvs = _131_1484}))))


let mk_Typ_meta : meta_t  ->  typ = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _131_1489 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _131_1489 t.pos))
end))


let mk_Typ_uvar' : (uvar_t * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_580 k' p -> (match (_30_580) with
| (u, k) -> begin
(let _131_1498 = (get_knd_ref k')
in (let _131_1497 = (mk_fvs ())
in (let _131_1496 = (mk_uvs ())
in {n = Typ_uvar (((u), (k))); tk = _131_1498; pos = p; fvs = _131_1497; uvs = _131_1496})))
end))


let mk_Typ_uvar : (uvar_t * knd)  ->  FStar_Range.range  ->  typ = (fun _30_585 p -> (match (_30_585) with
| (u, k) -> begin
(mk_Typ_uvar' ((u), (k)) (Some (k)) p)
end))


let mk_Typ_delayed : (typ * subst_t * typ memo)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _30_590 k p -> (match (_30_590) with
| (t, s, m) -> begin
(let _131_1518 = (match (t.n) with
| Typ_delayed (_30_594) -> begin
(failwith "NESTED DELAYED TYPES!")
end
| _30_597 -> begin
Typ_delayed (((FStar_Util.Inl (((t), (s)))), (m)))
end)
in (let _131_1517 = (FStar_Util.mk_ref k)
in (let _131_1516 = (mk_fvs ())
in (let _131_1515 = (mk_uvs ())
in {n = _131_1518; tk = _131_1517; pos = p; fvs = _131_1516; uvs = _131_1515}))))
end))


let mk_Typ_delayed' : ((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun st k p -> (let _131_1540 = (let _131_1536 = (let _131_1535 = (FStar_Util.mk_ref None)
in ((st), (_131_1535)))
in Typ_delayed (_131_1536))
in (let _131_1539 = (FStar_Util.mk_ref k)
in (let _131_1538 = (mk_fvs ())
in (let _131_1537 = (mk_uvs ())
in {n = _131_1540; tk = _131_1539; pos = p; fvs = _131_1538; uvs = _131_1537})))))


let mk_Typ_unknown : (typ', (knd', Prims.unit) syntax) syntax = (let _131_1543 = (get_knd_nref ())
in (let _131_1542 = (mk_fvs ())
in (let _131_1541 = (mk_uvs ())
in {n = Typ_unknown; tk = _131_1543; pos = dummyRange; fvs = _131_1542; uvs = _131_1541})))


let get_typ_nref : Prims.unit  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun _30_601 -> (match (()) with
| () -> begin
(

let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (

let _30_603 = (FStar_ST.op_Colon_Equals x None)
in x))
end))


let get_typ_ref : (typ', (knd', Prims.unit) syntax) syntax Prims.option  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun t -> (

let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (

let _30_607 = (FStar_ST.op_Colon_Equals x t)
in x)))


let mk_Total : typ  ->  comp = (fun t -> (let _131_1552 = (FStar_Util.mk_ref None)
in (let _131_1551 = (mk_fvs ())
in (let _131_1550 = (mk_uvs ())
in {n = Total (t); tk = _131_1552; pos = t.pos; fvs = _131_1551; uvs = _131_1550}))))


let mk_Comp : comp_typ  ->  comp = (fun ct -> (let _131_1557 = (FStar_Util.mk_ref None)
in (let _131_1556 = (mk_fvs ())
in (let _131_1555 = (mk_uvs ())
in {n = Comp (ct); tk = _131_1557; pos = ct.result_typ.pos; fvs = _131_1556; uvs = _131_1555}))))


let mk_Exp_bvar : bvvar  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun x t p -> (let _131_1566 = (get_typ_ref t)
in (let _131_1565 = (mk_fvs ())
in (let _131_1564 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _131_1566; pos = p; fvs = _131_1565; uvs = _131_1564}))))


let mk_Exp_fvar : (fvvar * fv_qual Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_616 t p -> (match (_30_616) with
| (x, b) -> begin
(let _131_1575 = (get_typ_ref t)
in (let _131_1574 = (mk_fvs ())
in (let _131_1573 = (mk_uvs ())
in {n = Exp_fvar (((x), (b))); tk = _131_1575; pos = p; fvs = _131_1574; uvs = _131_1573})))
end))


let mk_Exp_constant : sconst  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun s t p -> (let _131_1584 = (get_typ_ref t)
in (let _131_1583 = (mk_fvs ())
in (let _131_1582 = (mk_uvs ())
in {n = Exp_constant (s); tk = _131_1584; pos = p; fvs = _131_1583; uvs = _131_1582}))))


let mk_Exp_abs : (binders * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_624 t' p -> (match (_30_624) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _30_629 -> begin
(let _131_1593 = (get_typ_ref t')
in (let _131_1592 = (mk_fvs ())
in (let _131_1591 = (mk_uvs ())
in {n = Exp_abs (((b), (e))); tk = _131_1593; pos = p; fvs = _131_1592; uvs = _131_1591})))
end)
end))


let mk_Exp_abs' : (binders * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_632 t' p -> (match (_30_632) with
| (b, e) -> begin
(let _131_1603 = (match (((b), (e.n))) with
| (_30_636, Exp_abs ((b0)::bs, body)) -> begin
Exp_abs ((((FStar_List.append b ((b0)::bs))), (body)))
end
| ([], _30_646) -> begin
(failwith "abstraction with no binders!")
end
| _30_649 -> begin
Exp_abs (((b), (e)))
end)
in (let _131_1602 = (get_typ_ref t')
in (let _131_1601 = (mk_fvs ())
in (let _131_1600 = (mk_uvs ())
in {n = _131_1603; tk = _131_1602; pos = p; fvs = _131_1601; uvs = _131_1600}))))
end))


let mk_Exp_app : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_652 t p -> (match (_30_652) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _30_657 -> begin
(let _131_1612 = (get_typ_ref t)
in (let _131_1611 = (mk_fvs ())
in (let _131_1610 = (mk_uvs ())
in {n = Exp_app (((e1), (args))); tk = _131_1612; pos = p; fvs = _131_1611; uvs = _131_1610})))
end)
end))


let mk_Exp_app_flat : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_660 t p -> (match (_30_660) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app ((e1'), ((FStar_List.append args' args))) t p)
end
| _30_668 -> begin
(mk_Exp_app ((e1), (args)) t p)
end)
end))


let mk_Exp_app' : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_671 t p -> (match (_30_671) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _30_676 -> begin
(mk_Exp_app ((e1), (args)) t p)
end)
end))


let rec pat_vars : pat  ->  (btvdef, bvvdef) FStar_Util.either Prims.list = (fun p -> (match (p.v) with
| Pat_cons (_30_679, _30_681, ps) -> begin
(

let vars = (FStar_List.collect (fun _30_688 -> (match (_30_688) with
| (x, _30_687) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _30_703 -> begin
false
end)))) then begin
vars
end else begin
(Prims.raise (FStar_Errors.Error ((("Pattern variables may not occur more than once"), (p.p)))))
end)
end
| Pat_var (x) -> begin
(FStar_Util.Inr (x.v))::[]
end
| Pat_tvar (a) -> begin
(FStar_Util.Inl (a.v))::[]
end
| Pat_disj (ps) -> begin
(

let vars = (FStar_List.map pat_vars ps)
in if (not ((let _131_1633 = (FStar_List.tl vars)
in (let _131_1632 = (let _131_1631 = (let _131_1630 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _131_1630))
in (FStar_Util.for_all _131_1631))
in (FStar_All.pipe_right _131_1633 _131_1632))))) then begin
(

let vars = (let _131_1637 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _131_1636 = (FStar_List.map (fun _30_2 -> (match (_30_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.FStar_Ident.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idText
end)) v)
in (FStar_Util.concat_l ", " _131_1636)))))
in (FStar_Util.concat_l ";\n" _131_1637))
in (let _131_1640 = (let _131_1639 = (let _131_1638 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in ((_131_1638), (p.p)))
in FStar_Errors.Error (_131_1639))
in (Prims.raise _131_1640)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))


let mk_Exp_match : (exp * (pat * exp Prims.option * exp) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_735 t p -> (match (_30_735) with
| (e, pats) -> begin
(let _131_1649 = (get_typ_ref t)
in (let _131_1648 = (mk_fvs ())
in (let _131_1647 = (mk_uvs ())
in {n = Exp_match (((e), (pats))); tk = _131_1649; pos = p; fvs = _131_1648; uvs = _131_1647})))
end))


let mk_Exp_ascribed : (exp * typ * lident Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_741 t' p -> (match (_30_741) with
| (e, t, l) -> begin
(let _131_1658 = (get_typ_ref t')
in (let _131_1657 = (mk_fvs ())
in (let _131_1656 = (mk_uvs ())
in {n = Exp_ascribed (((e), (t), (l))); tk = _131_1658; pos = p; fvs = _131_1657; uvs = _131_1656})))
end))


let mk_Exp_let : (letbindings * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_746 t p -> (match (_30_746) with
| (lbs, e) -> begin
(let _131_1667 = (get_typ_ref t)
in (let _131_1666 = (mk_fvs ())
in (let _131_1665 = (mk_uvs ())
in {n = Exp_let (((lbs), (e))); tk = _131_1667; pos = p; fvs = _131_1666; uvs = _131_1665})))
end))


let mk_Exp_uvar' : (uvar_e * typ)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_751 t' p -> (match (_30_751) with
| (u, t) -> begin
(let _131_1676 = (get_typ_ref t')
in (let _131_1675 = (mk_fvs ())
in (let _131_1674 = (mk_uvs ())
in {n = Exp_uvar (((u), (t))); tk = _131_1676; pos = p; fvs = _131_1675; uvs = _131_1674})))
end))


let mk_Exp_uvar : (uvar_e * typ)  ->  FStar_Range.range  ->  exp = (fun _30_756 p -> (match (_30_756) with
| (u, t) -> begin
(mk_Exp_uvar' ((u), (t)) (Some (t)) p)
end))


let mk_Exp_delayed : (exp * subst_t * exp memo)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _30_761 t p -> (match (_30_761) with
| (e, s, m) -> begin
(let _131_1689 = (get_typ_ref t)
in (let _131_1688 = (mk_fvs ())
in (let _131_1687 = (mk_uvs ())
in {n = Exp_delayed (((e), (s), (m))); tk = _131_1689; pos = p; fvs = _131_1688; uvs = _131_1687})))
end))


let mk_Exp_meta' : meta_e  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun m t p -> (let _131_1698 = (get_typ_ref t)
in (let _131_1697 = (mk_fvs ())
in (let _131_1696 = (mk_uvs ())
in {n = Exp_meta (m); tk = _131_1698; pos = p; fvs = _131_1697; uvs = _131_1696}))))


let mk_Exp_meta : meta_e  ->  exp = (fun m -> (match (m) with
| Meta_desugared (e, _30_770) -> begin
(let _131_1701 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _131_1701 e.pos))
end))


let mk_lb : (lbname * lident * typ * exp)  ->  letbinding = (fun _30_777 -> (match (_30_777) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))


let mk_subst : subst  ->  subst = (fun s -> s)


let extend_subst : (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list = (fun x s -> (x)::s)


let argpos : arg  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _30_785) -> begin
t.pos
end
| (FStar_Util.Inr (e), _30_790) -> begin
e.pos
end))


let tun : typ = mk_Typ_unknown


let kun : knd = mk_Kind_unknown


let ktype : knd = mk_Kind_type


let keffect : knd = mk_Kind_effect


let null_id : ident = (mk_ident (("_"), (dummyRange)))


let null_bvd = {ppname = null_id; realname = null_id}


let null_bvar = (fun k -> {v = null_bvd; sort = k; p = dummyRange})


let t_binder : btvar  ->  binder = (fun a -> ((FStar_Util.Inl (a)), (None)))


let v_binder : bvvar  ->  binder = (fun a -> ((FStar_Util.Inr (a)), (None)))


let null_t_binder : knd  ->  binder = (fun t -> (let _131_1720 = (let _131_1719 = (null_bvar t)
in FStar_Util.Inl (_131_1719))
in ((_131_1720), (None))))


let null_v_binder : typ  ->  binder = (fun t -> (let _131_1724 = (let _131_1723 = (null_bvar t)
in FStar_Util.Inr (_131_1723))
in ((_131_1724), (None))))


let itarg : typ  ->  arg = (fun t -> ((FStar_Util.Inl (t)), (Some (Implicit (false)))))


let ivarg : exp  ->  arg = (fun v -> ((FStar_Util.Inr (v)), (Some (Implicit (false)))))


let targ : typ  ->  arg = (fun t -> ((FStar_Util.Inl (t)), (None)))


let varg : exp  ->  arg = (fun v -> ((FStar_Util.Inr (v)), (None)))


let is_null_pp = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))


let is_null_bvd = (fun b -> (b.realname.FStar_Ident.idText = null_id.FStar_Ident.idText))


let is_null_bvar = (fun b -> (is_null_bvd b.v))


let is_null_binder : binder  ->  Prims.bool = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _30_812) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _30_817) -> begin
(is_null_bvar x)
end))


let freevars_of_binders : binders  ->  freevars = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _30_3 -> (match (_30_3) with
| (FStar_Util.Inl (btv), _30_825) -> begin
(

let _30_827 = out
in (let _131_1745 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _131_1745; fxvs = _30_827.fxvs}))
end
| (FStar_Util.Inr (bxv), _30_832) -> begin
(

let _30_834 = out
in (let _131_1746 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _30_834.ftvs; fxvs = _131_1746}))
end)) no_fvs)))


let binders_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> ((t), (None))))))


let binders_of_freevars : freevars  ->  binders = (fun fvs -> (let _131_1755 = (let _131_1752 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _131_1752 (FStar_List.map t_binder)))
in (let _131_1754 = (let _131_1753 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _131_1753 (FStar_List.map v_binder)))
in (FStar_List.append _131_1755 _131_1754))))


let is_implicit : aqual  ->  Prims.bool = (fun _30_4 -> (match (_30_4) with
| Some (Implicit (_30_841)) -> begin
true
end
| _30_845 -> begin
false
end))


let as_implicit : Prims.bool  ->  aqual = (fun _30_5 -> (match (_30_5) with
| true -> begin
Some (Implicit (false))
end
| _30_849 -> begin
None
end))




