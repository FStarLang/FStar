
open Prims
type ident =
FStar_Ident.ident

type lident =
FStar_Ident.lid

type l__LongIdent =
lident

exception Err of (Prims.string)

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_24_7) -> begin
_24_7
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
| Error (_24_9) -> begin
_24_9
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
| Warning (_24_11) -> begin
_24_11
end))

type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}

let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

type 't var =
(lident, 't) withinfo_t

type fieldname =
lident

type 'a bvdef =
{ppname : ident; realname : ident}

let is_Mkbvdef = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbvdef"))))

type ('a, 't) bvar =
('a bvdef, 't) withinfo_t

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
| SetOptions (_24_27) -> begin
_24_27
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
| Typ_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Mkcomp_typ = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

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
| Kind_type -> begin
true
end
| _ -> begin
false
end))

let is_Kind_effect = (fun _discr_ -> (match (_discr_) with
| Kind_effect -> begin
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
| Kind_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Mkletbinding = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

let is_Mkfreevars = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfreevars"))))

let is_Mkuvars = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkuvars"))))

let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

let ___Typ_btvar____0 = (fun projectee -> (match (projectee) with
| Typ_btvar (_24_52) -> begin
_24_52
end))

let ___Typ_const____0 = (fun projectee -> (match (projectee) with
| Typ_const (_24_55) -> begin
_24_55
end))

let ___Typ_fun____0 = (fun projectee -> (match (projectee) with
| Typ_fun (_24_58) -> begin
_24_58
end))

let ___Typ_refine____0 = (fun projectee -> (match (projectee) with
| Typ_refine (_24_61) -> begin
_24_61
end))

let ___Typ_app____0 = (fun projectee -> (match (projectee) with
| Typ_app (_24_64) -> begin
_24_64
end))

let ___Typ_lam____0 = (fun projectee -> (match (projectee) with
| Typ_lam (_24_67) -> begin
_24_67
end))

let ___Typ_ascribed____0 = (fun projectee -> (match (projectee) with
| Typ_ascribed (_24_70) -> begin
_24_70
end))

let ___Typ_meta____0 = (fun projectee -> (match (projectee) with
| Typ_meta (_24_73) -> begin
_24_73
end))

let ___Typ_uvar____0 = (fun projectee -> (match (projectee) with
| Typ_uvar (_24_76) -> begin
_24_76
end))

let ___Typ_delayed____0 = (fun projectee -> (match (projectee) with
| Typ_delayed (_24_79) -> begin
_24_79
end))

let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_24_83) -> begin
_24_83
end))

let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_24_86) -> begin
_24_86
end))

let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_24_89) -> begin
_24_89
end))

let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_24_92) -> begin
_24_92
end))

let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_24_95) -> begin
_24_95
end))

let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_24_98) -> begin
_24_98
end))

let ___Meta_refresh_label____0 = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_24_101) -> begin
_24_101
end))

let ___Meta_slack_formula____0 = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_24_104) -> begin
_24_104
end))

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_24_107) -> begin
_24_107
end))

let ___Exp_bvar____0 = (fun projectee -> (match (projectee) with
| Exp_bvar (_24_110) -> begin
_24_110
end))

let ___Exp_fvar____0 = (fun projectee -> (match (projectee) with
| Exp_fvar (_24_113) -> begin
_24_113
end))

let ___Exp_constant____0 = (fun projectee -> (match (projectee) with
| Exp_constant (_24_116) -> begin
_24_116
end))

let ___Exp_abs____0 = (fun projectee -> (match (projectee) with
| Exp_abs (_24_119) -> begin
_24_119
end))

let ___Exp_app____0 = (fun projectee -> (match (projectee) with
| Exp_app (_24_122) -> begin
_24_122
end))

let ___Exp_match____0 = (fun projectee -> (match (projectee) with
| Exp_match (_24_125) -> begin
_24_125
end))

let ___Exp_ascribed____0 = (fun projectee -> (match (projectee) with
| Exp_ascribed (_24_128) -> begin
_24_128
end))

let ___Exp_let____0 = (fun projectee -> (match (projectee) with
| Exp_let (_24_131) -> begin
_24_131
end))

let ___Exp_uvar____0 = (fun projectee -> (match (projectee) with
| Exp_uvar (_24_134) -> begin
_24_134
end))

let ___Exp_delayed____0 = (fun projectee -> (match (projectee) with
| Exp_delayed (_24_137) -> begin
_24_137
end))

let ___Exp_meta____0 = (fun projectee -> (match (projectee) with
| Exp_meta (_24_140) -> begin
_24_140
end))

let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_24_142) -> begin
_24_142
end))

let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_24_145) -> begin
_24_145
end))

let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_24_148) -> begin
_24_148
end))

let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_24_151) -> begin
_24_151
end))

let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_24_154) -> begin
_24_154
end))

let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_24_157) -> begin
_24_157
end))

let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_24_160) -> begin
_24_160
end))

let ___Pat_tvar____0 = (fun projectee -> (match (projectee) with
| Pat_tvar (_24_163) -> begin
_24_163
end))

let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_24_166) -> begin
_24_166
end))

let ___Pat_twild____0 = (fun projectee -> (match (projectee) with
| Pat_twild (_24_169) -> begin
_24_169
end))

let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_24_172) -> begin
_24_172
end))

let ___Pat_dot_typ____0 = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_24_175) -> begin
_24_175
end))

let ___Kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Kind_abbrev (_24_178) -> begin
_24_178
end))

let ___Kind_arrow____0 = (fun projectee -> (match (projectee) with
| Kind_arrow (_24_181) -> begin
_24_181
end))

let ___Kind_uvar____0 = (fun projectee -> (match (projectee) with
| Kind_uvar (_24_184) -> begin
_24_184
end))

let ___Kind_lam____0 = (fun projectee -> (match (projectee) with
| Kind_lam (_24_187) -> begin
_24_187
end))

let ___Kind_delayed____0 = (fun projectee -> (match (projectee) with
| Kind_delayed (_24_190) -> begin
_24_190
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
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque -> begin
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

let ___Discriminator____0 = (fun projectee -> (match (projectee) with
| Discriminator (_24_197) -> begin
_24_197
end))

let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_24_200) -> begin
_24_200
end))

let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_24_203) -> begin
_24_203
end))

let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_24_206) -> begin
_24_206
end))

let ___DefaultEffect____0 = (fun projectee -> (match (projectee) with
| DefaultEffect (_24_209) -> begin
_24_209
end))

type tycon =
(lident * binders * knd)

type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

let is_Mkmonad_abbrev = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

type sub_eff =
{source : lident; target : lident; lift : typ}

let is_Mksub_eff = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

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

let is_Mkeff_decl = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

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
| Sig_tycon (_24_239) -> begin
_24_239
end))

let ___Sig_kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_24_242) -> begin
_24_242
end))

let ___Sig_typ_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_24_245) -> begin
_24_245
end))

let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_24_248) -> begin
_24_248
end))

let ___Sig_val_decl____0 = (fun projectee -> (match (projectee) with
| Sig_val_decl (_24_251) -> begin
_24_251
end))

let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_24_254) -> begin
_24_254
end))

let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_24_257) -> begin
_24_257
end))

let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_24_260) -> begin
_24_260
end))

let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_24_263) -> begin
_24_263
end))

let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_24_266) -> begin
_24_266
end))

let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_24_269) -> begin
_24_269
end))

let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_24_272) -> begin
_24_272
end))

let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_24_275) -> begin
_24_275
end))

type sigelts =
sigelt Prims.list

type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}

let is_Mkmodul = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

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
| K (_24_284) -> begin
_24_284
end))

let ___T____0 = (fun projectee -> (match (projectee) with
| T (_24_287) -> begin
_24_287
end))

let ___E____0 = (fun projectee -> (match (projectee) with
| E (_24_290) -> begin
_24_290
end))

let ___C____0 = (fun projectee -> (match (projectee) with
| C (_24_293) -> begin
_24_293
end))

type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

let is_Mklcomp = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

type path =
Prims.string Prims.list

let dummyRange = 0L

let withinfo = (fun v s r -> {v = v; sort = s; p = r})

let withsort = (fun v s -> (withinfo v s dummyRange))

let mk_ident = (fun _24_306 -> (match (_24_306) with
| (text, range) -> begin
{FStar_Ident.idText = text; FStar_Ident.idRange = range}
end))

let id_of_text = (fun str -> (mk_ident (str, dummyRange)))

let text_of_id = (fun id -> id.FStar_Ident.idText)

let text_of_path = (fun path -> (FStar_Util.concat_l "." path))

let path_of_text = (fun text -> (FStar_String.split (('.')::[]) text))

let path_of_ns = (fun ns -> (FStar_List.map text_of_id ns))

let path_of_lid = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))

let ids_of_lid = (fun lid -> (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))

let lid_of_ids = (fun ids -> (let _24_317 = (FStar_Util.prefix ids)
in (match (_24_317) with
| (ns, id) -> begin
(let nsstr = (let _77_1257 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _77_1257 text_of_path))
in {FStar_Ident.ns = ns; FStar_Ident.ident = id; FStar_Ident.nsstr = nsstr; FStar_Ident.str = if (nsstr = "") then begin
id.FStar_Ident.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.FStar_Ident.idText)
end})
end)))

let lid_of_path = (fun path pos -> (let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

let text_of_lid = (fun lid -> lid.FStar_Ident.str)

let lid_equals = (fun l1 l2 -> (l1.FStar_Ident.str = l2.FStar_Ident.str))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.FStar_Ident.idText = bvd2.realname.FStar_Ident.idText))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_24_332), FStar_Util.Inr (_24_335)) -> begin
(- (1))
end
| (FStar_Util.Inr (_24_339), FStar_Util.Inl (_24_342)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end))

let lid_with_range = (fun lid r -> (let id = (let _24_357 = lid.FStar_Ident.ident
in {FStar_Ident.idText = _24_357.FStar_Ident.idText; FStar_Ident.idRange = r})
in (let _24_360 = lid
in {FStar_Ident.ns = _24_360.FStar_Ident.ns; FStar_Ident.ident = id; FStar_Ident.nsstr = _24_360.FStar_Ident.nsstr; FStar_Ident.str = _24_360.FStar_Ident.str})))

let range_of_lid = (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idRange)

let range_of_lbname = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

let syn = (fun p k f -> (f k p))

let mk_fvs = (fun _24_371 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let mk_uvs = (fun _24_372 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let new_ftv_set = (fun _24_373 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.FStar_Ident.idText y.v.realname.FStar_Ident.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.FStar_Ident.idText)))
end))

let new_uv_set = (fun _24_377 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

let new_uvt_set = (fun _24_380 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _24_388 _24_392 -> (match ((_24_388, _24_392)) with
| ((x, _24_387), (y, _24_391)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _24_384 -> (match (_24_384) with
| (x, _24_383) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

let no_fvs = (let _77_1322 = (new_ftv_set ())
in (let _77_1321 = (new_ftv_set ())
in {ftvs = _77_1322; fxvs = _77_1321}))

let no_uvs = (let _77_1325 = (new_uv_set ())
in (let _77_1324 = (new_uvt_set ())
in (let _77_1323 = (new_uvt_set ())
in {uvars_k = _77_1325; uvars_t = _77_1324; uvars_e = _77_1323})))

let memo_no_uvs = (FStar_Util.mk_ref (Some (no_uvs)))

let memo_no_fvs = (FStar_Util.mk_ref (Some (no_fvs)))

let freevars_of_list = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _24_1 -> (match (_24_1) with
| FStar_Util.Inl (btv) -> begin
(let _24_398 = out
in (let _77_1330 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _77_1330; fxvs = _24_398.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(let _24_402 = out
in (let _77_1331 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _24_402.ftvs; fxvs = _77_1331}))
end)) no_fvs)))

let list_of_freevars = (fun fvs -> (let _77_1339 = (let _77_1335 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _77_1335 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _77_1338 = (let _77_1337 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _77_1337 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _77_1339 _77_1338))))

let get_unit_ref = (fun _24_407 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (())))
in (let _24_409 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let mk_Kind_type = (let _77_1344 = (get_unit_ref ())
in (let _77_1343 = (mk_fvs ())
in (let _77_1342 = (mk_uvs ())
in {n = Kind_type; tk = _77_1344; pos = dummyRange; fvs = _77_1343; uvs = _77_1342})))

let mk_Kind_effect = (let _77_1347 = (get_unit_ref ())
in (let _77_1346 = (mk_fvs ())
in (let _77_1345 = (mk_uvs ())
in {n = Kind_effect; tk = _77_1347; pos = dummyRange; fvs = _77_1346; uvs = _77_1345})))

let mk_Kind_abbrev = (fun _24_413 p -> (match (_24_413) with
| (kabr, k) -> begin
(let _77_1354 = (get_unit_ref ())
in (let _77_1353 = (mk_fvs ())
in (let _77_1352 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _77_1354; pos = p; fvs = _77_1353; uvs = _77_1352})))
end))

let mk_Kind_arrow = (fun _24_417 p -> (match (_24_417) with
| (bs, k) -> begin
(let _77_1361 = (get_unit_ref ())
in (let _77_1360 = (mk_fvs ())
in (let _77_1359 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _77_1361; pos = p; fvs = _77_1360; uvs = _77_1359})))
end))

let mk_Kind_arrow' = (fun _24_421 p -> (match (_24_421) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _24_425 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _24_431 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

let mk_Kind_uvar = (fun uv p -> (let _77_1372 = (get_unit_ref ())
in (let _77_1371 = (mk_fvs ())
in (let _77_1370 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _77_1372; pos = p; fvs = _77_1371; uvs = _77_1370}))))

let mk_Kind_lam = (fun _24_436 p -> (match (_24_436) with
| (vs, k) -> begin
(let _77_1379 = (get_unit_ref ())
in (let _77_1378 = (mk_fvs ())
in (let _77_1377 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _77_1379; pos = p; fvs = _77_1378; uvs = _77_1377})))
end))

let mk_Kind_delayed = (fun _24_441 p -> (match (_24_441) with
| (k, s, m) -> begin
(let _77_1386 = (get_unit_ref ())
in (let _77_1385 = (mk_fvs ())
in (let _77_1384 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _77_1386; pos = p; fvs = _77_1385; uvs = _77_1384})))
end))

let mk_Kind_unknown = (let _77_1389 = (get_unit_ref ())
in (let _77_1388 = (mk_fvs ())
in (let _77_1387 = (mk_uvs ())
in {n = Kind_unknown; tk = _77_1389; pos = dummyRange; fvs = _77_1388; uvs = _77_1387})))

let get_knd_nref = (fun _24_443 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _24_445 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_knd_ref = (fun k -> (let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _24_449 = (FStar_ST.op_Colon_Equals x k)
in x)))

let mk_Typ_btvar = (fun x k p -> (let _77_1402 = (get_knd_ref k)
in (let _77_1401 = (mk_fvs ())
in (let _77_1400 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _77_1402; pos = p; fvs = _77_1401; uvs = _77_1400}))))

let mk_Typ_const = (fun x k p -> (let _77_1409 = (get_knd_ref k)
in {n = Typ_const (x); tk = _77_1409; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _24_462 -> begin
Typ_fun ((bs, c))
end))

let mk_Typ_fun = (fun _24_465 k p -> (match (_24_465) with
| (bs, c) -> begin
(let _77_1422 = (check_fun bs c p)
in (let _77_1421 = (FStar_Util.mk_ref k)
in (let _77_1420 = (mk_fvs ())
in (let _77_1419 = (mk_uvs ())
in {n = _77_1422; tk = _77_1421; pos = p; fvs = _77_1420; uvs = _77_1419}))))
end))

let mk_Typ_refine = (fun _24_470 k p -> (match (_24_470) with
| (x, phi) -> begin
(let _77_1431 = (FStar_Util.mk_ref k)
in (let _77_1430 = (mk_fvs ())
in (let _77_1429 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _77_1431; pos = p; fvs = _77_1430; uvs = _77_1429})))
end))

let mk_Typ_app = (fun _24_475 k p -> (match (_24_475) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _24_480 -> begin
(let _77_1440 = (FStar_Util.mk_ref k)
in (let _77_1439 = (mk_fvs ())
in (let _77_1438 = (mk_uvs ())
in {n = Typ_app ((t1, args)); tk = _77_1440; pos = p; fvs = _77_1439; uvs = _77_1438})))
end)
end))

let mk_Typ_app' = (fun _24_483 k p -> (match (_24_483) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _24_488 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

let extend_typ_app = (fun _24_491 k p -> (match (_24_491) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _24_499 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

let mk_Typ_lam = (fun _24_502 k p -> (match (_24_502) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _24_507 -> begin
(let _77_1461 = (FStar_Util.mk_ref k)
in (let _77_1460 = (mk_fvs ())
in (let _77_1459 = (mk_uvs ())
in {n = Typ_lam ((b, t)); tk = _77_1461; pos = p; fvs = _77_1460; uvs = _77_1459})))
end)
end))

let mk_Typ_lam' = (fun _24_510 k p -> (match (_24_510) with
| (bs, t) -> begin
(mk_Typ_lam (bs, t) k p)
end))

let mk_Typ_ascribed' = (fun _24_515 k' p -> (match (_24_515) with
| (t, k) -> begin
(let _77_1476 = (FStar_Util.mk_ref k')
in (let _77_1475 = (mk_fvs ())
in (let _77_1474 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _77_1476; pos = p; fvs = _77_1475; uvs = _77_1474})))
end))

let mk_Typ_ascribed = (fun _24_520 p -> (match (_24_520) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

let mk_Typ_meta' = (fun m k p -> (let _77_1489 = (FStar_Util.mk_ref k)
in (let _77_1488 = (mk_fvs ())
in (let _77_1487 = (mk_uvs ())
in {n = Typ_meta (m); tk = _77_1489; pos = p; fvs = _77_1488; uvs = _77_1487}))))

let mk_Typ_meta = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _77_1492 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _77_1492 t.pos))
end))

let mk_Typ_uvar' = (fun _24_557 k' p -> (match (_24_557) with
| (u, k) -> begin
(let _77_1501 = (get_knd_ref k')
in (let _77_1500 = (mk_fvs ())
in (let _77_1499 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _77_1501; pos = p; fvs = _77_1500; uvs = _77_1499})))
end))

let mk_Typ_uvar = (fun _24_562 p -> (match (_24_562) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

let mk_Typ_delayed = (fun _24_567 k p -> (match (_24_567) with
| (t, s, m) -> begin
(let _77_1521 = (match (t.n) with
| Typ_delayed (_24_571) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _24_574 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _77_1520 = (FStar_Util.mk_ref k)
in (let _77_1519 = (mk_fvs ())
in (let _77_1518 = (mk_uvs ())
in {n = _77_1521; tk = _77_1520; pos = p; fvs = _77_1519; uvs = _77_1518}))))
end))

let mk_Typ_delayed' = (fun st k p -> (let _77_1543 = (let _77_1539 = (let _77_1538 = (FStar_Util.mk_ref None)
in (st, _77_1538))
in Typ_delayed (_77_1539))
in (let _77_1542 = (FStar_Util.mk_ref k)
in (let _77_1541 = (mk_fvs ())
in (let _77_1540 = (mk_uvs ())
in {n = _77_1543; tk = _77_1542; pos = p; fvs = _77_1541; uvs = _77_1540})))))

let mk_Typ_unknown = (let _77_1546 = (get_knd_nref ())
in (let _77_1545 = (mk_fvs ())
in (let _77_1544 = (mk_uvs ())
in {n = Typ_unknown; tk = _77_1546; pos = dummyRange; fvs = _77_1545; uvs = _77_1544})))

let get_typ_nref = (fun _24_578 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _24_580 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_typ_ref = (fun t -> (let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _24_584 = (FStar_ST.op_Colon_Equals x t)
in x)))

let mk_Total = (fun t -> (let _77_1555 = (FStar_Util.mk_ref None)
in (let _77_1554 = (mk_fvs ())
in (let _77_1553 = (mk_uvs ())
in {n = Total (t); tk = _77_1555; pos = t.pos; fvs = _77_1554; uvs = _77_1553}))))

let mk_Comp = (fun ct -> (let _77_1560 = (FStar_Util.mk_ref None)
in (let _77_1559 = (mk_fvs ())
in (let _77_1558 = (mk_uvs ())
in {n = Comp (ct); tk = _77_1560; pos = ct.result_typ.pos; fvs = _77_1559; uvs = _77_1558}))))

let mk_Exp_bvar = (fun x t p -> (let _77_1569 = (get_typ_ref t)
in (let _77_1568 = (mk_fvs ())
in (let _77_1567 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _77_1569; pos = p; fvs = _77_1568; uvs = _77_1567}))))

let mk_Exp_fvar = (fun _24_593 t p -> (match (_24_593) with
| (x, b) -> begin
(let _77_1578 = (get_typ_ref t)
in (let _77_1577 = (mk_fvs ())
in (let _77_1576 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _77_1578; pos = p; fvs = _77_1577; uvs = _77_1576})))
end))

let mk_Exp_constant = (fun s t p -> (let _77_1587 = (get_typ_ref t)
in (let _77_1586 = (mk_fvs ())
in (let _77_1585 = (mk_uvs ())
in {n = Exp_constant (s); tk = _77_1587; pos = p; fvs = _77_1586; uvs = _77_1585}))))

let mk_Exp_abs = (fun _24_601 t' p -> (match (_24_601) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _24_606 -> begin
(let _77_1596 = (get_typ_ref t')
in (let _77_1595 = (mk_fvs ())
in (let _77_1594 = (mk_uvs ())
in {n = Exp_abs ((b, e)); tk = _77_1596; pos = p; fvs = _77_1595; uvs = _77_1594})))
end)
end))

let mk_Exp_abs' = (fun _24_609 t' p -> (match (_24_609) with
| (b, e) -> begin
(let _77_1606 = (match ((b, e.n)) with
| (_24_613, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _24_623) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _24_626 -> begin
Exp_abs ((b, e))
end)
in (let _77_1605 = (get_typ_ref t')
in (let _77_1604 = (mk_fvs ())
in (let _77_1603 = (mk_uvs ())
in {n = _77_1606; tk = _77_1605; pos = p; fvs = _77_1604; uvs = _77_1603}))))
end))

let mk_Exp_app = (fun _24_629 t p -> (match (_24_629) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _24_634 -> begin
(let _77_1615 = (get_typ_ref t)
in (let _77_1614 = (mk_fvs ())
in (let _77_1613 = (mk_uvs ())
in {n = Exp_app ((e1, args)); tk = _77_1615; pos = p; fvs = _77_1614; uvs = _77_1613})))
end)
end))

let mk_Exp_app_flat = (fun _24_637 t p -> (match (_24_637) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _24_645 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let mk_Exp_app' = (fun _24_648 t p -> (match (_24_648) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _24_653 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let rec pat_vars = (fun p -> (match (p.v) with
| Pat_cons (_24_656, _24_658, ps) -> begin
(let vars = (FStar_List.collect (fun _24_665 -> (match (_24_665) with
| (x, _24_664) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _24_680 -> begin
false
end)))) then begin
vars
end else begin
(Prims.raise (Error (("Pattern variables may not occur more than once", p.p))))
end)
end
| Pat_var (x) -> begin
(FStar_Util.Inr (x.v))::[]
end
| Pat_tvar (a) -> begin
(FStar_Util.Inl (a.v))::[]
end
| Pat_disj (ps) -> begin
(let vars = (FStar_List.map pat_vars ps)
in if (not ((let _77_1636 = (FStar_List.tl vars)
in (let _77_1635 = (let _77_1634 = (let _77_1633 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _77_1633))
in (FStar_Util.for_all _77_1634))
in (FStar_All.pipe_right _77_1636 _77_1635))))) then begin
(let vars = (let _77_1640 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _77_1639 = (FStar_List.map (fun _24_2 -> (match (_24_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.FStar_Ident.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idText
end)) v)
in (FStar_Util.concat_l ", " _77_1639)))))
in (FStar_Util.concat_l ";\n" _77_1640))
in (let _77_1643 = (let _77_1642 = (let _77_1641 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_77_1641, p.p))
in Error (_77_1642))
in (Prims.raise _77_1643)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

let mk_Exp_match = (fun _24_712 t p -> (match (_24_712) with
| (e, pats) -> begin
(let _77_1652 = (get_typ_ref t)
in (let _77_1651 = (mk_fvs ())
in (let _77_1650 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _77_1652; pos = p; fvs = _77_1651; uvs = _77_1650})))
end))

let mk_Exp_ascribed = (fun _24_718 t' p -> (match (_24_718) with
| (e, t, l) -> begin
(let _77_1661 = (get_typ_ref t')
in (let _77_1660 = (mk_fvs ())
in (let _77_1659 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _77_1661; pos = p; fvs = _77_1660; uvs = _77_1659})))
end))

let mk_Exp_let = (fun _24_723 t p -> (match (_24_723) with
| (lbs, e) -> begin
(let _77_1670 = (get_typ_ref t)
in (let _77_1669 = (mk_fvs ())
in (let _77_1668 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _77_1670; pos = p; fvs = _77_1669; uvs = _77_1668})))
end))

let mk_Exp_uvar' = (fun _24_728 t' p -> (match (_24_728) with
| (u, t) -> begin
(let _77_1679 = (get_typ_ref t')
in (let _77_1678 = (mk_fvs ())
in (let _77_1677 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _77_1679; pos = p; fvs = _77_1678; uvs = _77_1677})))
end))

let mk_Exp_uvar = (fun _24_733 p -> (match (_24_733) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

let mk_Exp_delayed = (fun _24_738 t p -> (match (_24_738) with
| (e, s, m) -> begin
(let _77_1692 = (get_typ_ref t)
in (let _77_1691 = (mk_fvs ())
in (let _77_1690 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _77_1692; pos = p; fvs = _77_1691; uvs = _77_1690})))
end))

let mk_Exp_meta' = (fun m t p -> (let _77_1701 = (get_typ_ref t)
in (let _77_1700 = (mk_fvs ())
in (let _77_1699 = (mk_uvs ())
in {n = Exp_meta (m); tk = _77_1701; pos = p; fvs = _77_1700; uvs = _77_1699}))))

let mk_Exp_meta = (fun m -> (match (m) with
| Meta_desugared (e, _24_747) -> begin
(let _77_1704 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _77_1704 e.pos))
end))

let mk_lb = (fun _24_754 -> (match (_24_754) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst = (fun s -> s)

let extend_subst = (fun x s -> (x)::s)

let argpos = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _24_762) -> begin
t.pos
end
| (FStar_Util.Inr (e), _24_767) -> begin
e.pos
end))

let tun = mk_Typ_unknown

let kun = mk_Kind_unknown

let ktype = mk_Kind_type

let keffect = mk_Kind_effect

let null_id = (mk_ident ("_", dummyRange))

let null_bvd = {ppname = null_id; realname = null_id}

let null_bvar = (fun k -> {v = null_bvd; sort = k; p = dummyRange})

let t_binder = (fun a -> (FStar_Util.Inl (a), None))

let v_binder = (fun a -> (FStar_Util.Inr (a), None))

let null_t_binder = (fun t -> (FStar_Util.Inl ((null_bvar t)), None))

let null_v_binder = (fun t -> (FStar_Util.Inr ((null_bvar t)), None))

let itarg = (fun t -> (FStar_Util.Inl (t), Some (Implicit)))

let ivarg = (fun v -> (FStar_Util.Inr (v), Some (Implicit)))

let targ = (fun t -> (FStar_Util.Inl (t), None))

let varg = (fun v -> (FStar_Util.Inr (v), None))

let is_null_pp = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

let is_null_bvd = (fun b -> (b.realname.FStar_Ident.idText = null_id.FStar_Ident.idText))

let is_null_bvar = (fun b -> (is_null_bvd b.v))

let is_null_binder = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _24_789) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _24_794) -> begin
(is_null_bvar x)
end))

let freevars_of_binders = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _24_3 -> (match (_24_3) with
| (FStar_Util.Inl (btv), _24_802) -> begin
(let _24_804 = out
in (let _77_1741 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _77_1741; fxvs = _24_804.fxvs}))
end
| (FStar_Util.Inr (bxv), _24_809) -> begin
(let _24_811 = out
in (let _77_1742 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _24_811.ftvs; fxvs = _77_1742}))
end)) no_fvs)))

let binders_of_list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

let binders_of_freevars = (fun fvs -> (let _77_1751 = (let _77_1748 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _77_1748 (FStar_List.map t_binder)))
in (let _77_1750 = (let _77_1749 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _77_1749 (FStar_List.map v_binder)))
in (FStar_List.append _77_1751 _77_1750))))

let is_implicit = (fun _24_4 -> (match (_24_4) with
| Some (Implicit) -> begin
true
end
| _24_820 -> begin
false
end))

let as_implicit = (fun _24_5 -> (match (_24_5) with
| true -> begin
Some (Implicit)
end
| _24_824 -> begin
None
end))




