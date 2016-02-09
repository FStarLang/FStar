
open Prims
type ident =
FStar_Ident.ident

type lident =
FStar_Ident.lid

type l__LongIdent =
lident

exception Err of (Prims.string)

let is_Err : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_25_7) -> begin
_25_7
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
| Error (_25_9) -> begin
_25_9
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
| Warning (_25_11) -> begin
_25_11
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
| SetOptions (_25_27) -> begin
_25_27
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

let is_Typ_btvar : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_btvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_const : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_const (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_fun : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_refine : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_app : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_lam : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_lam (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_ascribed : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_meta : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_meta (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_uvar : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_delayed : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_unknown : typ'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Typ_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

let is_Total : comp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
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

let is_Meta_pattern : meta_t  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_named : meta_t  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_labeled : meta_t  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_refresh_label : meta_t  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_refresh_label (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_slack_formula : meta_t  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_Exp_bvar : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_bvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_fvar : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_constant : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_abs : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_app : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_match : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_match (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_ascribed : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_let : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_uvar : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_delayed : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_meta : exp'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exp_meta (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_desugared : meta_e  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
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

let is_Pat_disj : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
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

let is_Pat_tvar : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_tvar (_) -> begin
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

let is_Pat_twild : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_twild (_) -> begin
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

let is_Pat_dot_typ : pat'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pat_dot_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_type : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_type -> begin
true
end
| _ -> begin
false
end))

let is_Kind_effect : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_effect -> begin
true
end
| _ -> begin
false
end))

let is_Kind_abbrev : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_arrow : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_arrow (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_uvar : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_lam : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_lam (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_delayed : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_unknown : knd'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

let is_Mkfreevars : freevars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfreevars"))))

let is_Mkuvars : uvars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkuvars"))))

let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

let ___Typ_btvar____0 : typ'  ->  btvar = (fun projectee -> (match (projectee) with
| Typ_btvar (_25_52) -> begin
_25_52
end))

let ___Typ_const____0 : typ'  ->  ftvar = (fun projectee -> (match (projectee) with
| Typ_const (_25_55) -> begin
_25_55
end))

let ___Typ_fun____0 : typ'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Typ_fun (_25_58) -> begin
_25_58
end))

let ___Typ_refine____0 : typ'  ->  (bvvar * typ) = (fun projectee -> (match (projectee) with
| Typ_refine (_25_61) -> begin
_25_61
end))

let ___Typ_app____0 : typ'  ->  (typ * args) = (fun projectee -> (match (projectee) with
| Typ_app (_25_64) -> begin
_25_64
end))

let ___Typ_lam____0 : typ'  ->  (binders * typ) = (fun projectee -> (match (projectee) with
| Typ_lam (_25_67) -> begin
_25_67
end))

let ___Typ_ascribed____0 : typ'  ->  (typ * knd) = (fun projectee -> (match (projectee) with
| Typ_ascribed (_25_70) -> begin
_25_70
end))

let ___Typ_meta____0 : typ'  ->  meta_t = (fun projectee -> (match (projectee) with
| Typ_meta (_25_73) -> begin
_25_73
end))

let ___Typ_uvar____0 : typ'  ->  (uvar_t * knd) = (fun projectee -> (match (projectee) with
| Typ_uvar (_25_76) -> begin
_25_76
end))

let ___Typ_delayed____0 : typ'  ->  (((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either * typ memo) = (fun projectee -> (match (projectee) with
| Typ_delayed (_25_79) -> begin
_25_79
end))

let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_25_83) -> begin
_25_83
end))

let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_25_86) -> begin
_25_86
end))

let ___DECREASES____0 : cflags  ->  exp = (fun projectee -> (match (projectee) with
| DECREASES (_25_89) -> begin
_25_89
end))

let ___Meta_pattern____0 : meta_t  ->  (typ * arg Prims.list Prims.list) = (fun projectee -> (match (projectee) with
| Meta_pattern (_25_92) -> begin
_25_92
end))

let ___Meta_named____0 : meta_t  ->  (typ * lident) = (fun projectee -> (match (projectee) with
| Meta_named (_25_95) -> begin
_25_95
end))

let ___Meta_labeled____0 : meta_t  ->  (typ * Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_25_98) -> begin
_25_98
end))

let ___Meta_refresh_label____0 : meta_t  ->  (typ * Prims.bool Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_25_101) -> begin
_25_101
end))

let ___Meta_slack_formula____0 : meta_t  ->  (typ * typ * Prims.bool FStar_ST.ref) = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_25_104) -> begin
_25_104
end))

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_25_107) -> begin
_25_107
end))

let ___Exp_bvar____0 : exp'  ->  bvvar = (fun projectee -> (match (projectee) with
| Exp_bvar (_25_110) -> begin
_25_110
end))

let ___Exp_fvar____0 : exp'  ->  (fvvar * fv_qual Prims.option) = (fun projectee -> (match (projectee) with
| Exp_fvar (_25_113) -> begin
_25_113
end))

let ___Exp_constant____0 : exp'  ->  sconst = (fun projectee -> (match (projectee) with
| Exp_constant (_25_116) -> begin
_25_116
end))

let ___Exp_abs____0 : exp'  ->  (binders * exp) = (fun projectee -> (match (projectee) with
| Exp_abs (_25_119) -> begin
_25_119
end))

let ___Exp_app____0 : exp'  ->  (exp * args) = (fun projectee -> (match (projectee) with
| Exp_app (_25_122) -> begin
_25_122
end))

let ___Exp_match____0 : exp'  ->  (exp * (pat * exp Prims.option * exp) Prims.list) = (fun projectee -> (match (projectee) with
| Exp_match (_25_125) -> begin
_25_125
end))

let ___Exp_ascribed____0 : exp'  ->  (exp * typ * lident Prims.option) = (fun projectee -> (match (projectee) with
| Exp_ascribed (_25_128) -> begin
_25_128
end))

let ___Exp_let____0 : exp'  ->  (letbindings * exp) = (fun projectee -> (match (projectee) with
| Exp_let (_25_131) -> begin
_25_131
end))

let ___Exp_uvar____0 : exp'  ->  (uvar_e * typ) = (fun projectee -> (match (projectee) with
| Exp_uvar (_25_134) -> begin
_25_134
end))

let ___Exp_delayed____0 : exp'  ->  (exp * subst_t * exp memo) = (fun projectee -> (match (projectee) with
| Exp_delayed (_25_137) -> begin
_25_137
end))

let ___Exp_meta____0 : exp'  ->  meta_e = (fun projectee -> (match (projectee) with
| Exp_meta (_25_140) -> begin
_25_140
end))

let ___Meta_desugared____0 : meta_e  ->  (exp * meta_source_info) = (fun projectee -> (match (projectee) with
| Meta_desugared (_25_142) -> begin
_25_142
end))

let ___Record_projector____0 : fv_qual  ->  lident = (fun projectee -> (match (projectee) with
| Record_projector (_25_145) -> begin
_25_145
end))

let ___Record_ctor____0 : fv_qual  ->  (lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_25_148) -> begin
_25_148
end))

let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_25_151) -> begin
_25_151
end))

let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_25_154) -> begin
_25_154
end))

let ___Pat_cons____0 : pat'  ->  (fvvar * fv_qual Prims.option * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_25_157) -> begin
_25_157
end))

let ___Pat_var____0 : pat'  ->  bvvar = (fun projectee -> (match (projectee) with
| Pat_var (_25_160) -> begin
_25_160
end))

let ___Pat_tvar____0 : pat'  ->  btvar = (fun projectee -> (match (projectee) with
| Pat_tvar (_25_163) -> begin
_25_163
end))

let ___Pat_wild____0 : pat'  ->  bvvar = (fun projectee -> (match (projectee) with
| Pat_wild (_25_166) -> begin
_25_166
end))

let ___Pat_twild____0 : pat'  ->  btvar = (fun projectee -> (match (projectee) with
| Pat_twild (_25_169) -> begin
_25_169
end))

let ___Pat_dot_term____0 : pat'  ->  (bvvar * exp) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_25_172) -> begin
_25_172
end))

let ___Pat_dot_typ____0 : pat'  ->  (btvar * typ) = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_25_175) -> begin
_25_175
end))

let ___Kind_abbrev____0 : knd'  ->  (kabbrev * knd) = (fun projectee -> (match (projectee) with
| Kind_abbrev (_25_178) -> begin
_25_178
end))

let ___Kind_arrow____0 : knd'  ->  (binders * knd) = (fun projectee -> (match (projectee) with
| Kind_arrow (_25_181) -> begin
_25_181
end))

let ___Kind_uvar____0 : knd'  ->  uvar_k_app = (fun projectee -> (match (projectee) with
| Kind_uvar (_25_184) -> begin
_25_184
end))

let ___Kind_lam____0 : knd'  ->  (binders * knd) = (fun projectee -> (match (projectee) with
| Kind_lam (_25_187) -> begin
_25_187
end))

let ___Kind_delayed____0 : knd'  ->  (knd * subst_t * knd memo) = (fun projectee -> (match (projectee) with
| Kind_delayed (_25_190) -> begin
_25_190
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

let is_Private : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Assumption : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_Opaque : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Opaque -> begin
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

let ___Discriminator____0 : qualifier  ->  lident = (fun projectee -> (match (projectee) with
| Discriminator (_25_197) -> begin
_25_197
end))

let ___Projector____0 : qualifier  ->  (lident * (btvdef, bvvdef) FStar_Util.either) = (fun projectee -> (match (projectee) with
| Projector (_25_200) -> begin
_25_200
end))

let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_25_203) -> begin
_25_203
end))

let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_25_206) -> begin
_25_206
end))

let ___DefaultEffect____0 : qualifier  ->  lident Prims.option = (fun projectee -> (match (projectee) with
| DefaultEffect (_25_209) -> begin
_25_209
end))

type tycon =
(lident * binders * knd)

type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

type sub_eff =
{source : lident; target : lident; lift : typ}

let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

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

let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

let is_Sig_tycon : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_tycon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_kind_abbrev : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_typ_abbrev : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_typ_abbrev (_) -> begin
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

let is_Sig_val_decl : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_val_decl (_) -> begin
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

let is_Sig_bundle : sigelt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
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

let ___Sig_tycon____0 : sigelt  ->  (lident * binders * knd * lident Prims.list * lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_tycon (_25_239) -> begin
_25_239
end))

let ___Sig_kind_abbrev____0 : sigelt  ->  (lident * binders * knd * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_25_242) -> begin
_25_242
end))

let ___Sig_typ_abbrev____0 : sigelt  ->  (lident * binders * knd * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_25_245) -> begin
_25_245
end))

let ___Sig_datacon____0 : sigelt  ->  (lident * typ * tycon * qualifier Prims.list * lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_25_248) -> begin
_25_248
end))

let ___Sig_val_decl____0 : sigelt  ->  (lident * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_val_decl (_25_251) -> begin
_25_251
end))

let ___Sig_assume____0 : sigelt  ->  (lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_25_254) -> begin
_25_254
end))

let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_25_257) -> begin
_25_257
end))

let ___Sig_main____0 : sigelt  ->  (exp * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_25_260) -> begin
_25_260
end))

let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_25_263) -> begin
_25_263
end))

let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_25_266) -> begin
_25_266
end))

let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_25_269) -> begin
_25_269
end))

let ___Sig_effect_abbrev____0 : sigelt  ->  (lident * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_25_272) -> begin
_25_272
end))

let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_25_275) -> begin
_25_275
end))

type sigelts =
sigelt Prims.list

type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}

let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

type ktec =
| K of knd
| T of (typ * knd Prims.option)
| E of exp
| C of comp

let is_K : ktec  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| K (_) -> begin
true
end
| _ -> begin
false
end))

let is_T : ktec  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

let is_E : ktec  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| E (_) -> begin
true
end
| _ -> begin
false
end))

let is_C : ktec  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

let ___K____0 : ktec  ->  knd = (fun projectee -> (match (projectee) with
| K (_25_284) -> begin
_25_284
end))

let ___T____0 : ktec  ->  (typ * knd Prims.option) = (fun projectee -> (match (projectee) with
| T (_25_287) -> begin
_25_287
end))

let ___E____0 : ktec  ->  exp = (fun projectee -> (match (projectee) with
| E (_25_290) -> begin
_25_290
end))

let ___C____0 : ktec  ->  comp = (fun projectee -> (match (projectee) with
| C (_25_293) -> begin
_25_293
end))

type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

type path =
Prims.string Prims.list

let dummyRange : Prims.int64 = 0L

let withinfo = (fun v s r -> {v = v; sort = s; p = r})

let withsort = (fun v s -> (withinfo v s dummyRange))

let mk_ident : (Prims.string * FStar_Range.range)  ->  FStar_Ident.ident = (fun _25_306 -> (match (_25_306) with
| (text, range) -> begin
{FStar_Ident.idText = text; FStar_Ident.idRange = range}
end))

let id_of_text : Prims.string  ->  FStar_Ident.ident = (fun str -> (mk_ident (str, dummyRange)))

let text_of_id : ident  ->  Prims.string = (fun id -> id.FStar_Ident.idText)

let text_of_path : Prims.string Prims.list  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))

let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))

let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))

let path_of_lid : FStar_Ident.lident  ->  Prims.string Prims.list = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))

let ids_of_lid : FStar_Ident.lident  ->  FStar_Ident.ident Prims.list = (fun lid -> (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))

let lid_of_ids : ident Prims.list  ->  FStar_Ident.lident = (fun ids -> (let _25_317 = (FStar_Util.prefix ids)
in (match (_25_317) with
| (ns, id) -> begin
(let nsstr = (let _127_1257 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _127_1257 text_of_path))
in {FStar_Ident.ns = ns; FStar_Ident.ident = id; FStar_Ident.nsstr = nsstr; FStar_Ident.str = if (nsstr = "") then begin
id.FStar_Ident.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.FStar_Ident.idText)
end})
end)))

let lid_of_path : Prims.string Prims.list  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun path pos -> (let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

let text_of_lid : FStar_Ident.lident  ->  Prims.string = (fun lid -> lid.FStar_Ident.str)

let lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun l1 l2 -> (l1.FStar_Ident.str = l2.FStar_Ident.str))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.FStar_Ident.idText = bvd2.realname.FStar_Ident.idText))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_25_332), FStar_Util.Inr (_25_335)) -> begin
(- (1))
end
| (FStar_Util.Inr (_25_339), FStar_Util.Inl (_25_342)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end))

let lid_with_range : FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let id = (let _25_357 = lid.FStar_Ident.ident
in {FStar_Ident.idText = _25_357.FStar_Ident.idText; FStar_Ident.idRange = r})
in (let _25_360 = lid
in {FStar_Ident.ns = _25_360.FStar_Ident.ns; FStar_Ident.ident = id; FStar_Ident.nsstr = _25_360.FStar_Ident.nsstr; FStar_Ident.str = _25_360.FStar_Ident.str})))

let range_of_lid : FStar_Ident.lid  ->  FStar_Range.range = (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idRange)

let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

let syn = (fun p k f -> (f k p))

let mk_fvs = (fun _25_371 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let mk_uvs = (fun _25_372 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let new_ftv_set = (fun _25_373 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.FStar_Ident.idText y.v.realname.FStar_Ident.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.FStar_Ident.idText)))
end))

let new_uv_set = (fun _25_377 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

let new_uvt_set = (fun _25_380 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _25_388 _25_392 -> (match ((_25_388, _25_392)) with
| ((x, _25_387), (y, _25_391)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _25_384 -> (match (_25_384) with
| (x, _25_383) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

let no_fvs : freevars = (let _127_1322 = (new_ftv_set ())
in (let _127_1321 = (new_ftv_set ())
in {ftvs = _127_1322; fxvs = _127_1321}))

let no_uvs : uvars = (let _127_1325 = (new_uv_set ())
in (let _127_1324 = (new_uvt_set ())
in (let _127_1323 = (new_uvt_set ())
in {uvars_k = _127_1325; uvars_t = _127_1324; uvars_e = _127_1323})))

let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

let memo_no_fvs : freevars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_fvs)))

let freevars_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  freevars = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _25_1 -> (match (_25_1) with
| FStar_Util.Inl (btv) -> begin
(let _25_398 = out
in (let _127_1330 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _127_1330; fxvs = _25_398.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(let _25_402 = out
in (let _127_1331 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _25_402.ftvs; fxvs = _127_1331}))
end)) no_fvs)))

let list_of_freevars : freevars  ->  (btvar, bvvar) FStar_Util.either Prims.list = (fun fvs -> (let _127_1339 = (let _127_1335 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _127_1335 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _127_1338 = (let _127_1337 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _127_1337 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _127_1339 _127_1338))))

let get_unit_ref : Prims.unit  ->  Prims.unit Prims.option FStar_ST.ref = (fun _25_407 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (())))
in (let _25_409 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let mk_Kind_type : (knd', Prims.unit) syntax = (let _127_1344 = (get_unit_ref ())
in (let _127_1343 = (mk_fvs ())
in (let _127_1342 = (mk_uvs ())
in {n = Kind_type; tk = _127_1344; pos = dummyRange; fvs = _127_1343; uvs = _127_1342})))

let mk_Kind_effect : (knd', Prims.unit) syntax = (let _127_1347 = (get_unit_ref ())
in (let _127_1346 = (mk_fvs ())
in (let _127_1345 = (mk_uvs ())
in {n = Kind_effect; tk = _127_1347; pos = dummyRange; fvs = _127_1346; uvs = _127_1345})))

let mk_Kind_abbrev : (kabbrev * knd)  ->  FStar_Range.range  ->  knd = (fun _25_413 p -> (match (_25_413) with
| (kabr, k) -> begin
(let _127_1354 = (get_unit_ref ())
in (let _127_1353 = (mk_fvs ())
in (let _127_1352 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _127_1354; pos = p; fvs = _127_1353; uvs = _127_1352})))
end))

let mk_Kind_arrow : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _25_417 p -> (match (_25_417) with
| (bs, k) -> begin
(let _127_1361 = (get_unit_ref ())
in (let _127_1360 = (mk_fvs ())
in (let _127_1359 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _127_1361; pos = p; fvs = _127_1360; uvs = _127_1359})))
end))

let mk_Kind_arrow' : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * knd)  ->  FStar_Range.range  ->  knd = (fun _25_421 p -> (match (_25_421) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _25_425 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _25_431 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

let mk_Kind_uvar : uvar_k_app  ->  FStar_Range.range  ->  (knd', Prims.unit) syntax = (fun uv p -> (let _127_1372 = (get_unit_ref ())
in (let _127_1371 = (mk_fvs ())
in (let _127_1370 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _127_1372; pos = p; fvs = _127_1371; uvs = _127_1370}))))

let mk_Kind_lam : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _25_436 p -> (match (_25_436) with
| (vs, k) -> begin
(let _127_1379 = (get_unit_ref ())
in (let _127_1378 = (mk_fvs ())
in (let _127_1377 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _127_1379; pos = p; fvs = _127_1378; uvs = _127_1377})))
end))

let mk_Kind_delayed : (knd * subst_t * knd Prims.option FStar_ST.ref)  ->  FStar_Range.range  ->  knd = (fun _25_441 p -> (match (_25_441) with
| (k, s, m) -> begin
(let _127_1386 = (get_unit_ref ())
in (let _127_1385 = (mk_fvs ())
in (let _127_1384 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _127_1386; pos = p; fvs = _127_1385; uvs = _127_1384})))
end))

let mk_Kind_unknown : (knd', Prims.unit) syntax = (let _127_1389 = (get_unit_ref ())
in (let _127_1388 = (mk_fvs ())
in (let _127_1387 = (mk_uvs ())
in {n = Kind_unknown; tk = _127_1389; pos = dummyRange; fvs = _127_1388; uvs = _127_1387})))

let get_knd_nref : Prims.unit  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun _25_443 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _25_445 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_knd_ref : (knd', Prims.unit) syntax Prims.option  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun k -> (let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _25_449 = (FStar_ST.op_Colon_Equals x k)
in x)))

let mk_Typ_btvar : btvar  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun x k p -> (let _127_1402 = (get_knd_ref k)
in (let _127_1401 = (mk_fvs ())
in (let _127_1400 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _127_1402; pos = p; fvs = _127_1401; uvs = _127_1400}))))

let mk_Typ_const : ftvar  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun x k p -> (let _127_1409 = (get_knd_ref k)
in {n = Typ_const (x); tk = _127_1409; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _25_462 -> begin
Typ_fun ((bs, c))
end))

let mk_Typ_fun : (binders * comp)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_465 k p -> (match (_25_465) with
| (bs, c) -> begin
(let _127_1422 = (check_fun bs c p)
in (let _127_1421 = (FStar_Util.mk_ref k)
in (let _127_1420 = (mk_fvs ())
in (let _127_1419 = (mk_uvs ())
in {n = _127_1422; tk = _127_1421; pos = p; fvs = _127_1420; uvs = _127_1419}))))
end))

let mk_Typ_refine : (bvvar * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_470 k p -> (match (_25_470) with
| (x, phi) -> begin
(let _127_1431 = (FStar_Util.mk_ref k)
in (let _127_1430 = (mk_fvs ())
in (let _127_1429 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _127_1431; pos = p; fvs = _127_1430; uvs = _127_1429})))
end))

let mk_Typ_app : (typ * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_475 k p -> (match (_25_475) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _25_480 -> begin
(let _127_1440 = (FStar_Util.mk_ref k)
in (let _127_1439 = (mk_fvs ())
in (let _127_1438 = (mk_uvs ())
in {n = Typ_app ((t1, args)); tk = _127_1440; pos = p; fvs = _127_1439; uvs = _127_1438})))
end)
end))

let mk_Typ_app' : (typ * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_483 k p -> (match (_25_483) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _25_488 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

let extend_typ_app : ((typ', (knd', Prims.unit) syntax) syntax * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option))  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_491 k p -> (match (_25_491) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _25_499 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

let mk_Typ_lam : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_502 k p -> (match (_25_502) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _25_507 -> begin
(let _127_1461 = (FStar_Util.mk_ref k)
in (let _127_1460 = (mk_fvs ())
in (let _127_1459 = (mk_uvs ())
in {n = Typ_lam ((b, t)); tk = _127_1461; pos = p; fvs = _127_1460; uvs = _127_1459})))
end)
end))

let mk_Typ_lam' : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_510 k p -> (match (_25_510) with
| (bs, t) -> begin
(mk_Typ_lam (bs, t) k p)
end))

let mk_Typ_ascribed' : (typ * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_515 k' p -> (match (_25_515) with
| (t, k) -> begin
(let _127_1476 = (FStar_Util.mk_ref k')
in (let _127_1475 = (mk_fvs ())
in (let _127_1474 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _127_1476; pos = p; fvs = _127_1475; uvs = _127_1474})))
end))

let mk_Typ_ascribed : (typ * knd)  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_520 p -> (match (_25_520) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

let mk_Typ_meta' : meta_t  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun m k p -> (let _127_1489 = (FStar_Util.mk_ref k)
in (let _127_1488 = (mk_fvs ())
in (let _127_1487 = (mk_uvs ())
in {n = Typ_meta (m); tk = _127_1489; pos = p; fvs = _127_1488; uvs = _127_1487}))))

let mk_Typ_meta : meta_t  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _127_1492 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _127_1492 t.pos))
end))

let mk_Typ_uvar' : (uvar_t * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_557 k' p -> (match (_25_557) with
| (u, k) -> begin
(let _127_1501 = (get_knd_ref k')
in (let _127_1500 = (mk_fvs ())
in (let _127_1499 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _127_1501; pos = p; fvs = _127_1500; uvs = _127_1499})))
end))

let mk_Typ_uvar : (uvar_t * knd)  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_562 p -> (match (_25_562) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

let mk_Typ_delayed : ((typ', (knd', Prims.unit) syntax) syntax * subst_t * typ Prims.option FStar_ST.ref)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_567 k p -> (match (_25_567) with
| (t, s, m) -> begin
(let _127_1521 = (match (t.n) with
| Typ_delayed (_25_571) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _25_574 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _127_1520 = (FStar_Util.mk_ref k)
in (let _127_1519 = (mk_fvs ())
in (let _127_1518 = (mk_uvs ())
in {n = _127_1521; tk = _127_1520; pos = p; fvs = _127_1519; uvs = _127_1518}))))
end))

let mk_Typ_delayed' : ((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun st k p -> (let _127_1543 = (let _127_1539 = (let _127_1538 = (FStar_Util.mk_ref None)
in (st, _127_1538))
in Typ_delayed (_127_1539))
in (let _127_1542 = (FStar_Util.mk_ref k)
in (let _127_1541 = (mk_fvs ())
in (let _127_1540 = (mk_uvs ())
in {n = _127_1543; tk = _127_1542; pos = p; fvs = _127_1541; uvs = _127_1540})))))

let mk_Typ_unknown : (typ', (knd', Prims.unit) syntax) syntax = (let _127_1546 = (get_knd_nref ())
in (let _127_1545 = (mk_fvs ())
in (let _127_1544 = (mk_uvs ())
in {n = Typ_unknown; tk = _127_1546; pos = dummyRange; fvs = _127_1545; uvs = _127_1544})))

let get_typ_nref : Prims.unit  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun _25_578 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _25_580 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_typ_ref : (typ', (knd', Prims.unit) syntax) syntax Prims.option  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun t -> (let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _25_584 = (FStar_ST.op_Colon_Equals x t)
in x)))

let mk_Total : typ  ->  (comp', Prims.unit) syntax = (fun t -> (let _127_1555 = (FStar_Util.mk_ref None)
in (let _127_1554 = (mk_fvs ())
in (let _127_1553 = (mk_uvs ())
in {n = Total (t); tk = _127_1555; pos = t.pos; fvs = _127_1554; uvs = _127_1553}))))

let mk_Comp : comp_typ  ->  (comp', Prims.unit) syntax = (fun ct -> (let _127_1560 = (FStar_Util.mk_ref None)
in (let _127_1559 = (mk_fvs ())
in (let _127_1558 = (mk_uvs ())
in {n = Comp (ct); tk = _127_1560; pos = ct.result_typ.pos; fvs = _127_1559; uvs = _127_1558}))))

let mk_Exp_bvar : bvvar  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun x t p -> (let _127_1569 = (get_typ_ref t)
in (let _127_1568 = (mk_fvs ())
in (let _127_1567 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _127_1569; pos = p; fvs = _127_1568; uvs = _127_1567}))))

let mk_Exp_fvar : (fvvar * fv_qual Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_593 t p -> (match (_25_593) with
| (x, b) -> begin
(let _127_1578 = (get_typ_ref t)
in (let _127_1577 = (mk_fvs ())
in (let _127_1576 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _127_1578; pos = p; fvs = _127_1577; uvs = _127_1576})))
end))

let mk_Exp_constant : sconst  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun s t p -> (let _127_1587 = (get_typ_ref t)
in (let _127_1586 = (mk_fvs ())
in (let _127_1585 = (mk_uvs ())
in {n = Exp_constant (s); tk = _127_1587; pos = p; fvs = _127_1586; uvs = _127_1585}))))

let mk_Exp_abs : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_601 t' p -> (match (_25_601) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _25_606 -> begin
(let _127_1596 = (get_typ_ref t')
in (let _127_1595 = (mk_fvs ())
in (let _127_1594 = (mk_uvs ())
in {n = Exp_abs ((b, e)); tk = _127_1596; pos = p; fvs = _127_1595; uvs = _127_1594})))
end)
end))

let mk_Exp_abs' : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_609 t' p -> (match (_25_609) with
| (b, e) -> begin
(let _127_1606 = (match ((b, e.n)) with
| (_25_613, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _25_623) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _25_626 -> begin
Exp_abs ((b, e))
end)
in (let _127_1605 = (get_typ_ref t')
in (let _127_1604 = (mk_fvs ())
in (let _127_1603 = (mk_uvs ())
in {n = _127_1606; tk = _127_1605; pos = p; fvs = _127_1604; uvs = _127_1603}))))
end))

let mk_Exp_app : (exp * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_629 t p -> (match (_25_629) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _25_634 -> begin
(let _127_1615 = (get_typ_ref t)
in (let _127_1614 = (mk_fvs ())
in (let _127_1613 = (mk_uvs ())
in {n = Exp_app ((e1, args)); tk = _127_1615; pos = p; fvs = _127_1614; uvs = _127_1613})))
end)
end))

let mk_Exp_app_flat : ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_637 t p -> (match (_25_637) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _25_645 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let mk_Exp_app' : (exp * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_648 t p -> (match (_25_648) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _25_653 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let rec pat_vars : (pat', ((knd', Prims.unit) syntax, (typ', (knd', Prims.unit) syntax) syntax) FStar_Util.either Prims.option) withinfo_t  ->  ((typ', (knd', Prims.unit) syntax) syntax bvdef, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef) FStar_Util.either Prims.list = (fun p -> (match (p.v) with
| Pat_cons (_25_656, _25_658, ps) -> begin
(let vars = (FStar_List.collect (fun _25_665 -> (match (_25_665) with
| (x, _25_664) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _25_680 -> begin
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
in if (not ((let _127_1636 = (FStar_List.tl vars)
in (let _127_1635 = (let _127_1634 = (let _127_1633 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _127_1633))
in (FStar_Util.for_all _127_1634))
in (FStar_All.pipe_right _127_1636 _127_1635))))) then begin
(let vars = (let _127_1640 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _127_1639 = (FStar_List.map (fun _25_2 -> (match (_25_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.FStar_Ident.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idText
end)) v)
in (FStar_Util.concat_l ", " _127_1639)))))
in (FStar_Util.concat_l ";\n" _127_1640))
in (let _127_1643 = (let _127_1642 = (let _127_1641 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_127_1641, p.p))
in Error (_127_1642))
in (Prims.raise _127_1643)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

let mk_Exp_match : (exp * (pat * exp Prims.option * exp) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_712 t p -> (match (_25_712) with
| (e, pats) -> begin
(let _127_1652 = (get_typ_ref t)
in (let _127_1651 = (mk_fvs ())
in (let _127_1650 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _127_1652; pos = p; fvs = _127_1651; uvs = _127_1650})))
end))

let mk_Exp_ascribed : (exp * typ * lident Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_718 t' p -> (match (_25_718) with
| (e, t, l) -> begin
(let _127_1661 = (get_typ_ref t')
in (let _127_1660 = (mk_fvs ())
in (let _127_1659 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _127_1661; pos = p; fvs = _127_1660; uvs = _127_1659})))
end))

let mk_Exp_let : (letbindings * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_723 t p -> (match (_25_723) with
| (lbs, e) -> begin
(let _127_1670 = (get_typ_ref t)
in (let _127_1669 = (mk_fvs ())
in (let _127_1668 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _127_1670; pos = p; fvs = _127_1669; uvs = _127_1668})))
end))

let mk_Exp_uvar' : (uvar_e * typ)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_728 t' p -> (match (_25_728) with
| (u, t) -> begin
(let _127_1679 = (get_typ_ref t')
in (let _127_1678 = (mk_fvs ())
in (let _127_1677 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _127_1679; pos = p; fvs = _127_1678; uvs = _127_1677})))
end))

let mk_Exp_uvar : (uvar_e * typ)  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_733 p -> (match (_25_733) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

let mk_Exp_delayed : (exp * subst_t * exp Prims.option FStar_ST.ref)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_738 t p -> (match (_25_738) with
| (e, s, m) -> begin
(let _127_1692 = (get_typ_ref t)
in (let _127_1691 = (mk_fvs ())
in (let _127_1690 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _127_1692; pos = p; fvs = _127_1691; uvs = _127_1690})))
end))

let mk_Exp_meta' : meta_e  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun m t p -> (let _127_1701 = (get_typ_ref t)
in (let _127_1700 = (mk_fvs ())
in (let _127_1699 = (mk_uvs ())
in {n = Exp_meta (m); tk = _127_1701; pos = p; fvs = _127_1700; uvs = _127_1699}))))

let mk_Exp_meta : meta_e  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun m -> (match (m) with
| Meta_desugared (e, _25_747) -> begin
(let _127_1704 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _127_1704 e.pos))
end))

let mk_lb : (lbname * lident * typ * exp)  ->  letbinding = (fun _25_754 -> (match (_25_754) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst : subst  ->  subst = (fun s -> s)

let extend_subst : (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list = (fun x s -> (x)::s)

let argpos : arg  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _25_762) -> begin
t.pos
end
| (FStar_Util.Inr (e), _25_767) -> begin
e.pos
end))

let tun : (typ', (knd', Prims.unit) syntax) syntax = mk_Typ_unknown

let kun : (knd', Prims.unit) syntax = mk_Kind_unknown

let ktype : (knd', Prims.unit) syntax = mk_Kind_type

let keffect : (knd', Prims.unit) syntax = mk_Kind_effect

let null_id : FStar_Ident.ident = (mk_ident ("_", dummyRange))

let null_bvd = {ppname = null_id; realname = null_id}

let null_bvar = (fun k -> {v = null_bvd; sort = k; p = dummyRange})

let t_binder : btvar  ->  ((btvar, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) = (fun a -> (FStar_Util.Inl (a), None))

let v_binder : bvvar  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, bvvar) FStar_Util.either * arg_qualifier Prims.option) = (fun a -> (FStar_Util.Inr (a), None))

let null_t_binder : (knd', Prims.unit) syntax  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inl ((null_bvar t)), None))

let null_v_binder : (typ', (knd', Prims.unit) syntax) syntax  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inr ((null_bvar t)), None))

let itarg : (typ', (knd', Prims.unit) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inl (t), Some (Implicit)))

let ivarg : (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun v -> (FStar_Util.Inr (v), Some (Implicit)))

let targ : (typ', (knd', Prims.unit) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inl (t), None))

let varg : (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun v -> (FStar_Util.Inr (v), None))

let is_null_pp = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

let is_null_bvd = (fun b -> (b.realname.FStar_Ident.idText = null_id.FStar_Ident.idText))

let is_null_bvar = (fun b -> (is_null_bvd b.v))

let is_null_binder : binder  ->  Prims.bool = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _25_789) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _25_794) -> begin
(is_null_bvar x)
end))

let freevars_of_binders : binders  ->  freevars = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _25_3 -> (match (_25_3) with
| (FStar_Util.Inl (btv), _25_802) -> begin
(let _25_804 = out
in (let _127_1741 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _127_1741; fxvs = _25_804.fxvs}))
end
| (FStar_Util.Inr (bxv), _25_809) -> begin
(let _25_811 = out
in (let _127_1742 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _25_811.ftvs; fxvs = _127_1742}))
end)) no_fvs)))

let binders_of_list : (((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either Prims.list  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

let binders_of_freevars : freevars  ->  ((btvar, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list = (fun fvs -> (let _127_1751 = (let _127_1748 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _127_1748 (FStar_List.map t_binder)))
in (let _127_1750 = (let _127_1749 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _127_1749 (FStar_List.map v_binder)))
in (FStar_List.append _127_1751 _127_1750))))

let is_implicit : arg_qualifier Prims.option  ->  Prims.bool = (fun _25_4 -> (match (_25_4) with
| Some (Implicit) -> begin
true
end
| _25_820 -> begin
false
end))

let as_implicit : Prims.bool  ->  arg_qualifier Prims.option = (fun _25_5 -> (match (_25_5) with
| true -> begin
Some (Implicit)
end
| _25_824 -> begin
None
end))




