
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
| Err (_23_7) -> begin
_23_7
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
| Error (_23_9) -> begin
_23_9
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
| Warning (_23_11) -> begin
_23_11
end))

type ident =
{idText : Prims.string; idRange : FStar_Range.range}

let is_Mkident = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkident"))))

type l__LongIdent =
{ns : ident Prims.list; ident : ident; nsstr : Prims.string; str : Prims.string}

let is_MkLongIdent = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_MkLongIdent"))))

type lident =
l__LongIdent

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
| Const_unit
| Const_uint8 of Prims.byte
| Const_bool of Prims.bool
| Const_int32 of Prims.int32
| Const_int64 of Prims.int64
| Const_int of Prims.string
| Const_char of Prims.char
| Const_float of Prims.double
| Const_bytearray of (Prims.byte Prims.array * FStar_Range.range)
| Const_string of (Prims.byte Prims.array * FStar_Range.range)

let is_Const_unit = (fun _discr_ -> (match (_discr_) with
| Const_unit -> begin
true
end
| _ -> begin
false
end))

let is_Const_uint8 = (fun _discr_ -> (match (_discr_) with
| Const_uint8 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_bool = (fun _discr_ -> (match (_discr_) with
| Const_bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int32 = (fun _discr_ -> (match (_discr_) with
| Const_int32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int64 = (fun _discr_ -> (match (_discr_) with
| Const_int64 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int = (fun _discr_ -> (match (_discr_) with
| Const_int (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_char = (fun _discr_ -> (match (_discr_) with
| Const_char (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_float = (fun _discr_ -> (match (_discr_) with
| Const_float (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_bytearray = (fun _discr_ -> (match (_discr_) with
| Const_bytearray (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_string = (fun _discr_ -> (match (_discr_) with
| Const_string (_) -> begin
true
end
| _ -> begin
false
end))

let ___Const_uint8____0 = (fun projectee -> (match (projectee) with
| Const_uint8 (_23_35) -> begin
_23_35
end))

let ___Const_bool____0 = (fun projectee -> (match (projectee) with
| Const_bool (_23_38) -> begin
_23_38
end))

let ___Const_int32____0 = (fun projectee -> (match (projectee) with
| Const_int32 (_23_41) -> begin
_23_41
end))

let ___Const_int64____0 = (fun projectee -> (match (projectee) with
| Const_int64 (_23_44) -> begin
_23_44
end))

let ___Const_int____0 = (fun projectee -> (match (projectee) with
| Const_int (_23_47) -> begin
_23_47
end))

let ___Const_char____0 = (fun projectee -> (match (projectee) with
| Const_char (_23_50) -> begin
_23_50
end))

let ___Const_float____0 = (fun projectee -> (match (projectee) with
| Const_float (_23_53) -> begin
_23_53
end))

let ___Const_bytearray____0 = (fun projectee -> (match (projectee) with
| Const_bytearray (_23_56) -> begin
_23_56
end))

let ___Const_string____0 = (fun projectee -> (match (projectee) with
| Const_string (_23_59) -> begin
_23_59
end))

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
| SetOptions (_23_62) -> begin
_23_62
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
| Typ_btvar (_23_87) -> begin
_23_87
end))

let ___Typ_const____0 = (fun projectee -> (match (projectee) with
| Typ_const (_23_90) -> begin
_23_90
end))

let ___Typ_fun____0 = (fun projectee -> (match (projectee) with
| Typ_fun (_23_93) -> begin
_23_93
end))

let ___Typ_refine____0 = (fun projectee -> (match (projectee) with
| Typ_refine (_23_96) -> begin
_23_96
end))

let ___Typ_app____0 = (fun projectee -> (match (projectee) with
| Typ_app (_23_99) -> begin
_23_99
end))

let ___Typ_lam____0 = (fun projectee -> (match (projectee) with
| Typ_lam (_23_102) -> begin
_23_102
end))

let ___Typ_ascribed____0 = (fun projectee -> (match (projectee) with
| Typ_ascribed (_23_105) -> begin
_23_105
end))

let ___Typ_meta____0 = (fun projectee -> (match (projectee) with
| Typ_meta (_23_108) -> begin
_23_108
end))

let ___Typ_uvar____0 = (fun projectee -> (match (projectee) with
| Typ_uvar (_23_111) -> begin
_23_111
end))

let ___Typ_delayed____0 = (fun projectee -> (match (projectee) with
| Typ_delayed (_23_114) -> begin
_23_114
end))

let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_23_118) -> begin
_23_118
end))

let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_23_121) -> begin
_23_121
end))

let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_23_124) -> begin
_23_124
end))

let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_23_127) -> begin
_23_127
end))

let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_23_130) -> begin
_23_130
end))

let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_23_133) -> begin
_23_133
end))

let ___Meta_refresh_label____0 = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_23_136) -> begin
_23_136
end))

let ___Meta_slack_formula____0 = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_23_139) -> begin
_23_139
end))

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_23_142) -> begin
_23_142
end))

let ___Exp_bvar____0 = (fun projectee -> (match (projectee) with
| Exp_bvar (_23_145) -> begin
_23_145
end))

let ___Exp_fvar____0 = (fun projectee -> (match (projectee) with
| Exp_fvar (_23_148) -> begin
_23_148
end))

let ___Exp_constant____0 = (fun projectee -> (match (projectee) with
| Exp_constant (_23_151) -> begin
_23_151
end))

let ___Exp_abs____0 = (fun projectee -> (match (projectee) with
| Exp_abs (_23_154) -> begin
_23_154
end))

let ___Exp_app____0 = (fun projectee -> (match (projectee) with
| Exp_app (_23_157) -> begin
_23_157
end))

let ___Exp_match____0 = (fun projectee -> (match (projectee) with
| Exp_match (_23_160) -> begin
_23_160
end))

let ___Exp_ascribed____0 = (fun projectee -> (match (projectee) with
| Exp_ascribed (_23_163) -> begin
_23_163
end))

let ___Exp_let____0 = (fun projectee -> (match (projectee) with
| Exp_let (_23_166) -> begin
_23_166
end))

let ___Exp_uvar____0 = (fun projectee -> (match (projectee) with
| Exp_uvar (_23_169) -> begin
_23_169
end))

let ___Exp_delayed____0 = (fun projectee -> (match (projectee) with
| Exp_delayed (_23_172) -> begin
_23_172
end))

let ___Exp_meta____0 = (fun projectee -> (match (projectee) with
| Exp_meta (_23_175) -> begin
_23_175
end))

let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_23_177) -> begin
_23_177
end))

let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_23_180) -> begin
_23_180
end))

let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_23_183) -> begin
_23_183
end))

let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_23_186) -> begin
_23_186
end))

let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_23_189) -> begin
_23_189
end))

let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_23_192) -> begin
_23_192
end))

let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_23_195) -> begin
_23_195
end))

let ___Pat_tvar____0 = (fun projectee -> (match (projectee) with
| Pat_tvar (_23_198) -> begin
_23_198
end))

let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_23_201) -> begin
_23_201
end))

let ___Pat_twild____0 = (fun projectee -> (match (projectee) with
| Pat_twild (_23_204) -> begin
_23_204
end))

let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_23_207) -> begin
_23_207
end))

let ___Pat_dot_typ____0 = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_23_210) -> begin
_23_210
end))

let ___Kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Kind_abbrev (_23_213) -> begin
_23_213
end))

let ___Kind_arrow____0 = (fun projectee -> (match (projectee) with
| Kind_arrow (_23_216) -> begin
_23_216
end))

let ___Kind_uvar____0 = (fun projectee -> (match (projectee) with
| Kind_uvar (_23_219) -> begin
_23_219
end))

let ___Kind_lam____0 = (fun projectee -> (match (projectee) with
| Kind_lam (_23_222) -> begin
_23_222
end))

let ___Kind_delayed____0 = (fun projectee -> (match (projectee) with
| Kind_delayed (_23_225) -> begin
_23_225
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
| Discriminator (_23_232) -> begin
_23_232
end))

let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_23_235) -> begin
_23_235
end))

let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_23_238) -> begin
_23_238
end))

let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_23_241) -> begin
_23_241
end))

let ___DefaultEffect____0 = (fun projectee -> (match (projectee) with
| DefaultEffect (_23_244) -> begin
_23_244
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
| Sig_tycon (_23_274) -> begin
_23_274
end))

let ___Sig_kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_23_277) -> begin
_23_277
end))

let ___Sig_typ_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_23_280) -> begin
_23_280
end))

let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_23_283) -> begin
_23_283
end))

let ___Sig_val_decl____0 = (fun projectee -> (match (projectee) with
| Sig_val_decl (_23_286) -> begin
_23_286
end))

let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_23_289) -> begin
_23_289
end))

let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_23_292) -> begin
_23_292
end))

let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_23_295) -> begin
_23_295
end))

let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_23_298) -> begin
_23_298
end))

let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_23_301) -> begin
_23_301
end))

let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_23_304) -> begin
_23_304
end))

let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_23_307) -> begin
_23_307
end))

let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_23_310) -> begin
_23_310
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
| K (_23_319) -> begin
_23_319
end))

let ___T____0 = (fun projectee -> (match (projectee) with
| T (_23_322) -> begin
_23_322
end))

let ___E____0 = (fun projectee -> (match (projectee) with
| E (_23_325) -> begin
_23_325
end))

let ___C____0 = (fun projectee -> (match (projectee) with
| C (_23_328) -> begin
_23_328
end))

type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

let is_Mklcomp = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

type path =
Prims.string Prims.list

let dummyRange = 0L

let withinfo = (fun v s r -> {v = v; sort = s; p = r})

let withsort = (fun v s -> (withinfo v s dummyRange))

let mk_ident = (fun _23_341 -> (match (_23_341) with
| (text, range) -> begin
{idText = text; idRange = range}
end))

let id_of_text = (fun str -> (mk_ident (str, dummyRange)))

let text_of_id = (fun id -> id.idText)

let text_of_path = (fun path -> (FStar_Util.concat_l "." path))

let path_of_text = (fun text -> (FStar_String.split (('.')::[]) text))

let path_of_ns = (fun ns -> (FStar_List.map text_of_id ns))

let path_of_lid = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.ns ((lid.ident)::[]))))

let ids_of_lid = (fun lid -> (FStar_List.append lid.ns ((lid.ident)::[])))

let lid_of_ids = (fun ids -> (let _23_352 = (FStar_Util.prefix ids)
in (match (_23_352) with
| (ns, id) -> begin
(let nsstr = (let _89_1404 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _89_1404 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = if (nsstr = "") then begin
id.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.idText)
end})
end)))

let lid_of_path = (fun path pos -> (let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

let text_of_lid = (fun lid -> lid.str)

let lid_equals = (fun l1 l2 -> (l1.str = l2.str))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.idText = bvd2.realname.idText))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_23_367), FStar_Util.Inr (_23_370)) -> begin
(- (1))
end
| (FStar_Util.Inr (_23_374), FStar_Util.Inl (_23_377)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.idText y.realname.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.idText y.realname.idText)
end))

let lid_with_range = (fun lid r -> (let id = (let _23_392 = lid.ident
in {idText = _23_392.idText; idRange = r})
in (let _23_395 = lid
in {ns = _23_395.ns; ident = id; nsstr = _23_395.nsstr; str = _23_395.str})))

let range_of_lid = (fun lid -> lid.ident.idRange)

let range_of_lbname = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

let syn = (fun p k f -> (f k p))

let mk_fvs = (fun _23_406 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let mk_uvs = (fun _23_407 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let new_ftv_set = (fun _23_408 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.idText y.v.realname.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.idText)))
end))

let new_uv_set = (fun _23_412 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

let new_uvt_set = (fun _23_415 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _23_423 _23_427 -> (match ((_23_423, _23_427)) with
| ((x, _23_422), (y, _23_426)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _23_419 -> (match (_23_419) with
| (x, _23_418) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

let no_fvs = (let _89_1453 = (new_ftv_set ())
in (let _89_1452 = (new_ftv_set ())
in {ftvs = _89_1453; fxvs = _89_1452}))

let no_uvs = (let _89_1456 = (new_uv_set ())
in (let _89_1455 = (new_uvt_set ())
in (let _89_1454 = (new_uvt_set ())
in {uvars_k = _89_1456; uvars_t = _89_1455; uvars_e = _89_1454})))

let memo_no_uvs = (FStar_Util.mk_ref (Some (no_uvs)))

let memo_no_fvs = (FStar_Util.mk_ref (Some (no_fvs)))

let freevars_of_list = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _23_1 -> (match (_23_1) with
| FStar_Util.Inl (btv) -> begin
(let _23_433 = out
in (let _89_1461 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _89_1461; fxvs = _23_433.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(let _23_437 = out
in (let _89_1462 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _23_437.ftvs; fxvs = _89_1462}))
end)) no_fvs)))

let list_of_freevars = (fun fvs -> (let _89_1470 = (let _89_1466 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _89_1466 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _89_1469 = (let _89_1468 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _89_1468 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _89_1470 _89_1469))))

let get_unit_ref = (fun _23_442 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (())))
in (let _23_444 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let mk_Kind_type = (let _89_1475 = (get_unit_ref ())
in (let _89_1474 = (mk_fvs ())
in (let _89_1473 = (mk_uvs ())
in {n = Kind_type; tk = _89_1475; pos = dummyRange; fvs = _89_1474; uvs = _89_1473})))

let mk_Kind_effect = (let _89_1478 = (get_unit_ref ())
in (let _89_1477 = (mk_fvs ())
in (let _89_1476 = (mk_uvs ())
in {n = Kind_effect; tk = _89_1478; pos = dummyRange; fvs = _89_1477; uvs = _89_1476})))

let mk_Kind_abbrev = (fun _23_448 p -> (match (_23_448) with
| (kabr, k) -> begin
(let _89_1485 = (get_unit_ref ())
in (let _89_1484 = (mk_fvs ())
in (let _89_1483 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _89_1485; pos = p; fvs = _89_1484; uvs = _89_1483})))
end))

let mk_Kind_arrow = (fun _23_452 p -> (match (_23_452) with
| (bs, k) -> begin
(let _89_1492 = (get_unit_ref ())
in (let _89_1491 = (mk_fvs ())
in (let _89_1490 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _89_1492; pos = p; fvs = _89_1491; uvs = _89_1490})))
end))

let mk_Kind_arrow' = (fun _23_456 p -> (match (_23_456) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _23_460 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _23_466 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

let mk_Kind_uvar = (fun uv p -> (let _89_1503 = (get_unit_ref ())
in (let _89_1502 = (mk_fvs ())
in (let _89_1501 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _89_1503; pos = p; fvs = _89_1502; uvs = _89_1501}))))

let mk_Kind_lam = (fun _23_471 p -> (match (_23_471) with
| (vs, k) -> begin
(let _89_1510 = (get_unit_ref ())
in (let _89_1509 = (mk_fvs ())
in (let _89_1508 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _89_1510; pos = p; fvs = _89_1509; uvs = _89_1508})))
end))

let mk_Kind_delayed = (fun _23_476 p -> (match (_23_476) with
| (k, s, m) -> begin
(let _89_1517 = (get_unit_ref ())
in (let _89_1516 = (mk_fvs ())
in (let _89_1515 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _89_1517; pos = p; fvs = _89_1516; uvs = _89_1515})))
end))

let mk_Kind_unknown = (let _89_1520 = (get_unit_ref ())
in (let _89_1519 = (mk_fvs ())
in (let _89_1518 = (mk_uvs ())
in {n = Kind_unknown; tk = _89_1520; pos = dummyRange; fvs = _89_1519; uvs = _89_1518})))

let get_knd_nref = (fun _23_478 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _23_480 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_knd_ref = (fun k -> (let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _23_484 = (FStar_ST.op_Colon_Equals x k)
in x)))

let mk_Typ_btvar = (fun x k p -> (let _89_1533 = (get_knd_ref k)
in (let _89_1532 = (mk_fvs ())
in (let _89_1531 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _89_1533; pos = p; fvs = _89_1532; uvs = _89_1531}))))

let mk_Typ_const = (fun x k p -> (let _89_1540 = (get_knd_ref k)
in {n = Typ_const (x); tk = _89_1540; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _23_497 -> begin
Typ_fun ((bs, c))
end))

let mk_Typ_fun = (fun _23_500 k p -> (match (_23_500) with
| (bs, c) -> begin
(let _89_1553 = (check_fun bs c p)
in (let _89_1552 = (FStar_Util.mk_ref k)
in (let _89_1551 = (mk_fvs ())
in (let _89_1550 = (mk_uvs ())
in {n = _89_1553; tk = _89_1552; pos = p; fvs = _89_1551; uvs = _89_1550}))))
end))

let mk_Typ_refine = (fun _23_505 k p -> (match (_23_505) with
| (x, phi) -> begin
(let _89_1562 = (FStar_Util.mk_ref k)
in (let _89_1561 = (mk_fvs ())
in (let _89_1560 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _89_1562; pos = p; fvs = _89_1561; uvs = _89_1560})))
end))

let mk_Typ_app = (fun _23_510 k p -> (match (_23_510) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _23_515 -> begin
(let _89_1571 = (FStar_Util.mk_ref k)
in (let _89_1570 = (mk_fvs ())
in (let _89_1569 = (mk_uvs ())
in {n = Typ_app ((t1, args)); tk = _89_1571; pos = p; fvs = _89_1570; uvs = _89_1569})))
end)
end))

let mk_Typ_app' = (fun _23_518 k p -> (match (_23_518) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _23_523 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

let extend_typ_app = (fun _23_526 k p -> (match (_23_526) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _23_534 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

let mk_Typ_lam = (fun _23_537 k p -> (match (_23_537) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _23_542 -> begin
(let _89_1592 = (FStar_Util.mk_ref k)
in (let _89_1591 = (mk_fvs ())
in (let _89_1590 = (mk_uvs ())
in {n = Typ_lam ((b, t)); tk = _89_1592; pos = p; fvs = _89_1591; uvs = _89_1590})))
end)
end))

let mk_Typ_lam' = (fun _23_545 k p -> (match (_23_545) with
| (bs, t) -> begin
(mk_Typ_lam (bs, t) k p)
end))

let mk_Typ_ascribed' = (fun _23_550 k' p -> (match (_23_550) with
| (t, k) -> begin
(let _89_1607 = (FStar_Util.mk_ref k')
in (let _89_1606 = (mk_fvs ())
in (let _89_1605 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _89_1607; pos = p; fvs = _89_1606; uvs = _89_1605})))
end))

let mk_Typ_ascribed = (fun _23_555 p -> (match (_23_555) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

let mk_Typ_meta' = (fun m k p -> (let _89_1620 = (FStar_Util.mk_ref k)
in (let _89_1619 = (mk_fvs ())
in (let _89_1618 = (mk_uvs ())
in {n = Typ_meta (m); tk = _89_1620; pos = p; fvs = _89_1619; uvs = _89_1618}))))

let mk_Typ_meta = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _89_1623 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _89_1623 t.pos))
end))

let mk_Typ_uvar' = (fun _23_592 k' p -> (match (_23_592) with
| (u, k) -> begin
(let _89_1632 = (get_knd_ref k')
in (let _89_1631 = (mk_fvs ())
in (let _89_1630 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _89_1632; pos = p; fvs = _89_1631; uvs = _89_1630})))
end))

let mk_Typ_uvar = (fun _23_597 p -> (match (_23_597) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

let mk_Typ_delayed = (fun _23_602 k p -> (match (_23_602) with
| (t, s, m) -> begin
(let _89_1652 = (match (t.n) with
| Typ_delayed (_23_606) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _23_609 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _89_1651 = (FStar_Util.mk_ref k)
in (let _89_1650 = (mk_fvs ())
in (let _89_1649 = (mk_uvs ())
in {n = _89_1652; tk = _89_1651; pos = p; fvs = _89_1650; uvs = _89_1649}))))
end))

let mk_Typ_delayed' = (fun st k p -> (let _89_1674 = (let _89_1670 = (let _89_1669 = (FStar_Util.mk_ref None)
in (st, _89_1669))
in Typ_delayed (_89_1670))
in (let _89_1673 = (FStar_Util.mk_ref k)
in (let _89_1672 = (mk_fvs ())
in (let _89_1671 = (mk_uvs ())
in {n = _89_1674; tk = _89_1673; pos = p; fvs = _89_1672; uvs = _89_1671})))))

let mk_Typ_unknown = (let _89_1677 = (get_knd_nref ())
in (let _89_1676 = (mk_fvs ())
in (let _89_1675 = (mk_uvs ())
in {n = Typ_unknown; tk = _89_1677; pos = dummyRange; fvs = _89_1676; uvs = _89_1675})))

let get_typ_nref = (fun _23_613 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _23_615 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_typ_ref = (fun t -> (let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _23_619 = (FStar_ST.op_Colon_Equals x t)
in x)))

let mk_Total = (fun t -> (let _89_1686 = (FStar_Util.mk_ref None)
in (let _89_1685 = (mk_fvs ())
in (let _89_1684 = (mk_uvs ())
in {n = Total (t); tk = _89_1686; pos = t.pos; fvs = _89_1685; uvs = _89_1684}))))

let mk_Comp = (fun ct -> (let _89_1691 = (FStar_Util.mk_ref None)
in (let _89_1690 = (mk_fvs ())
in (let _89_1689 = (mk_uvs ())
in {n = Comp (ct); tk = _89_1691; pos = ct.result_typ.pos; fvs = _89_1690; uvs = _89_1689}))))

let mk_Exp_bvar = (fun x t p -> (let _89_1700 = (get_typ_ref t)
in (let _89_1699 = (mk_fvs ())
in (let _89_1698 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _89_1700; pos = p; fvs = _89_1699; uvs = _89_1698}))))

let mk_Exp_fvar = (fun _23_628 t p -> (match (_23_628) with
| (x, b) -> begin
(let _89_1709 = (get_typ_ref t)
in (let _89_1708 = (mk_fvs ())
in (let _89_1707 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _89_1709; pos = p; fvs = _89_1708; uvs = _89_1707})))
end))

let mk_Exp_constant = (fun s t p -> (let _89_1718 = (get_typ_ref t)
in (let _89_1717 = (mk_fvs ())
in (let _89_1716 = (mk_uvs ())
in {n = Exp_constant (s); tk = _89_1718; pos = p; fvs = _89_1717; uvs = _89_1716}))))

let mk_Exp_abs = (fun _23_636 t' p -> (match (_23_636) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _23_641 -> begin
(let _89_1727 = (get_typ_ref t')
in (let _89_1726 = (mk_fvs ())
in (let _89_1725 = (mk_uvs ())
in {n = Exp_abs ((b, e)); tk = _89_1727; pos = p; fvs = _89_1726; uvs = _89_1725})))
end)
end))

let mk_Exp_abs' = (fun _23_644 t' p -> (match (_23_644) with
| (b, e) -> begin
(let _89_1737 = (match ((b, e.n)) with
| (_23_648, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _23_658) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _23_661 -> begin
Exp_abs ((b, e))
end)
in (let _89_1736 = (get_typ_ref t')
in (let _89_1735 = (mk_fvs ())
in (let _89_1734 = (mk_uvs ())
in {n = _89_1737; tk = _89_1736; pos = p; fvs = _89_1735; uvs = _89_1734}))))
end))

let mk_Exp_app = (fun _23_664 t p -> (match (_23_664) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _23_669 -> begin
(let _89_1746 = (get_typ_ref t)
in (let _89_1745 = (mk_fvs ())
in (let _89_1744 = (mk_uvs ())
in {n = Exp_app ((e1, args)); tk = _89_1746; pos = p; fvs = _89_1745; uvs = _89_1744})))
end)
end))

let mk_Exp_app_flat = (fun _23_672 t p -> (match (_23_672) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _23_680 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let mk_Exp_app' = (fun _23_683 t p -> (match (_23_683) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _23_688 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let rec pat_vars = (fun p -> (match (p.v) with
| Pat_cons (_23_691, _23_693, ps) -> begin
(let vars = (FStar_List.collect (fun _23_700 -> (match (_23_700) with
| (x, _23_699) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _23_715 -> begin
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
in if (not ((let _89_1767 = (FStar_List.tl vars)
in (let _89_1766 = (let _89_1765 = (let _89_1764 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _89_1764))
in (FStar_Util.for_all _89_1765))
in (FStar_All.pipe_right _89_1767 _89_1766))))) then begin
(let vars = (let _89_1771 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _89_1770 = (FStar_List.map (fun _23_2 -> (match (_23_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.idText
end)) v)
in (FStar_Util.concat_l ", " _89_1770)))))
in (FStar_Util.concat_l ";\n" _89_1771))
in (let _89_1774 = (let _89_1773 = (let _89_1772 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_89_1772, p.p))
in Error (_89_1773))
in (Prims.raise _89_1774)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

let mk_Exp_match = (fun _23_747 t p -> (match (_23_747) with
| (e, pats) -> begin
(let _89_1783 = (get_typ_ref t)
in (let _89_1782 = (mk_fvs ())
in (let _89_1781 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _89_1783; pos = p; fvs = _89_1782; uvs = _89_1781})))
end))

let mk_Exp_ascribed = (fun _23_753 t' p -> (match (_23_753) with
| (e, t, l) -> begin
(let _89_1792 = (get_typ_ref t')
in (let _89_1791 = (mk_fvs ())
in (let _89_1790 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _89_1792; pos = p; fvs = _89_1791; uvs = _89_1790})))
end))

let mk_Exp_let = (fun _23_758 t p -> (match (_23_758) with
| (lbs, e) -> begin
(let _89_1801 = (get_typ_ref t)
in (let _89_1800 = (mk_fvs ())
in (let _89_1799 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _89_1801; pos = p; fvs = _89_1800; uvs = _89_1799})))
end))

let mk_Exp_uvar' = (fun _23_763 t' p -> (match (_23_763) with
| (u, t) -> begin
(let _89_1810 = (get_typ_ref t')
in (let _89_1809 = (mk_fvs ())
in (let _89_1808 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _89_1810; pos = p; fvs = _89_1809; uvs = _89_1808})))
end))

let mk_Exp_uvar = (fun _23_768 p -> (match (_23_768) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

let mk_Exp_delayed = (fun _23_773 t p -> (match (_23_773) with
| (e, s, m) -> begin
(let _89_1823 = (get_typ_ref t)
in (let _89_1822 = (mk_fvs ())
in (let _89_1821 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _89_1823; pos = p; fvs = _89_1822; uvs = _89_1821})))
end))

let mk_Exp_meta' = (fun m t p -> (let _89_1832 = (get_typ_ref t)
in (let _89_1831 = (mk_fvs ())
in (let _89_1830 = (mk_uvs ())
in {n = Exp_meta (m); tk = _89_1832; pos = p; fvs = _89_1831; uvs = _89_1830}))))

let mk_Exp_meta = (fun m -> (match (m) with
| Meta_desugared (e, _23_782) -> begin
(let _89_1835 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _89_1835 e.pos))
end))

let mk_lb = (fun _23_789 -> (match (_23_789) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst = (fun s -> s)

let extend_subst = (fun x s -> (x)::s)

let argpos = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _23_797) -> begin
t.pos
end
| (FStar_Util.Inr (e), _23_802) -> begin
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

let null_t_binder = (fun t -> (let _89_1854 = (let _89_1853 = (null_bvar t)
in FStar_Util.Inl (_89_1853))
in (_89_1854, None)))

let null_v_binder = (fun t -> (let _89_1858 = (let _89_1857 = (null_bvar t)
in FStar_Util.Inr (_89_1857))
in (_89_1858, None)))

let itarg = (fun t -> (FStar_Util.Inl (t), Some (Implicit)))

let ivarg = (fun v -> (FStar_Util.Inr (v), Some (Implicit)))

let targ = (fun t -> (FStar_Util.Inl (t), None))

let varg = (fun v -> (FStar_Util.Inr (v), None))

let is_null_pp = (fun b -> (b.ppname.idText = null_id.idText))

let is_null_bvd = (fun b -> (b.realname.idText = null_id.idText))

let is_null_bvar = (fun b -> (is_null_bvd b.v))

let is_null_binder = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _23_824) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _23_829) -> begin
(is_null_bvar x)
end))

let freevars_of_binders = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _23_3 -> (match (_23_3) with
| (FStar_Util.Inl (btv), _23_837) -> begin
(let _23_839 = out
in (let _89_1879 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _89_1879; fxvs = _23_839.fxvs}))
end
| (FStar_Util.Inr (bxv), _23_844) -> begin
(let _23_846 = out
in (let _89_1880 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _23_846.ftvs; fxvs = _89_1880}))
end)) no_fvs)))

let binders_of_list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

let binders_of_freevars = (fun fvs -> (let _89_1889 = (let _89_1886 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _89_1886 (FStar_List.map t_binder)))
in (let _89_1888 = (let _89_1887 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _89_1887 (FStar_List.map v_binder)))
in (FStar_List.append _89_1889 _89_1888))))

let is_implicit = (fun _23_4 -> (match (_23_4) with
| Some (Implicit) -> begin
true
end
| _23_855 -> begin
false
end))

let as_implicit = (fun _23_5 -> (match (_23_5) with
| true -> begin
Some (Implicit)
end
| _23_859 -> begin
None
end))




