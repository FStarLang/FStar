
exception Err of (Prims.string)

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_22_7) -> begin
_22_7
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
| Error (_22_9) -> begin
_22_9
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
| Warning (_22_11) -> begin
_22_11
end))

type ident =
{idText : Prims.string; idRange : FStar_Range.range}

let is_Mkident = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkident"))

type l__LongIdent =
{ns : ident Prims.list; ident : ident; nsstr : Prims.string; str : Prims.string}

let is_MkLongIdent = (fun _ -> (FStar_All.failwith "Not yet implemented:is_MkLongIdent"))

type lident =
l__LongIdent

type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}

let is_Mkwithinfo_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))

type 't var =
(lident, 't) withinfo_t

type fieldname =
lident

type 'a bvdef =
{ppname : ident; realname : ident}

let is_Mkbvdef = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbvdef"))

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
| Const_uint8 (_22_35) -> begin
_22_35
end))

let ___Const_bool____0 = (fun projectee -> (match (projectee) with
| Const_bool (_22_38) -> begin
_22_38
end))

let ___Const_int32____0 = (fun projectee -> (match (projectee) with
| Const_int32 (_22_41) -> begin
_22_41
end))

let ___Const_int64____0 = (fun projectee -> (match (projectee) with
| Const_int64 (_22_44) -> begin
_22_44
end))

let ___Const_int____0 = (fun projectee -> (match (projectee) with
| Const_int (_22_47) -> begin
_22_47
end))

let ___Const_char____0 = (fun projectee -> (match (projectee) with
| Const_char (_22_50) -> begin
_22_50
end))

let ___Const_float____0 = (fun projectee -> (match (projectee) with
| Const_float (_22_53) -> begin
_22_53
end))

let ___Const_bytearray____0 = (fun projectee -> (match (projectee) with
| Const_bytearray (_22_56) -> begin
_22_56
end))

let ___Const_string____0 = (fun projectee -> (match (projectee) with
| Const_string (_22_59) -> begin
_22_59
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
| SetOptions (_22_62) -> begin
_22_62
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
| Meta_pattern of (typ * arg Prims.list)
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
| MaskedEffect 
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

let is_Mkcomp_typ = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))

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

let is_MaskedEffect = (fun _discr_ -> (match (_discr_) with
| MaskedEffect -> begin
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

let is_Mkletbinding = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))

let is_Mkfreevars = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfreevars"))

let is_Mkuvars = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkuvars"))

let is_Mksyntax = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))

let ___Typ_btvar____0 = (fun projectee -> (match (projectee) with
| Typ_btvar (_22_87) -> begin
_22_87
end))

let ___Typ_const____0 = (fun projectee -> (match (projectee) with
| Typ_const (_22_90) -> begin
_22_90
end))

let ___Typ_fun____0 = (fun projectee -> (match (projectee) with
| Typ_fun (_22_93) -> begin
_22_93
end))

let ___Typ_refine____0 = (fun projectee -> (match (projectee) with
| Typ_refine (_22_96) -> begin
_22_96
end))

let ___Typ_app____0 = (fun projectee -> (match (projectee) with
| Typ_app (_22_99) -> begin
_22_99
end))

let ___Typ_lam____0 = (fun projectee -> (match (projectee) with
| Typ_lam (_22_102) -> begin
_22_102
end))

let ___Typ_ascribed____0 = (fun projectee -> (match (projectee) with
| Typ_ascribed (_22_105) -> begin
_22_105
end))

let ___Typ_meta____0 = (fun projectee -> (match (projectee) with
| Typ_meta (_22_108) -> begin
_22_108
end))

let ___Typ_uvar____0 = (fun projectee -> (match (projectee) with
| Typ_uvar (_22_111) -> begin
_22_111
end))

let ___Typ_delayed____0 = (fun projectee -> (match (projectee) with
| Typ_delayed (_22_114) -> begin
_22_114
end))

let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_22_118) -> begin
_22_118
end))

let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_22_121) -> begin
_22_121
end))

let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_22_124) -> begin
_22_124
end))

let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_22_127) -> begin
_22_127
end))

let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_22_130) -> begin
_22_130
end))

let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_22_133) -> begin
_22_133
end))

let ___Meta_refresh_label____0 = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_22_136) -> begin
_22_136
end))

let ___Meta_slack_formula____0 = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_22_139) -> begin
_22_139
end))

let ___Fixed____1 = (fun projectee -> (match (projectee) with
| Fixed (_22_144) -> begin
_22_144
end))

let ___Exp_bvar____0 = (fun projectee -> (match (projectee) with
| Exp_bvar (_22_147) -> begin
_22_147
end))

let ___Exp_fvar____0 = (fun projectee -> (match (projectee) with
| Exp_fvar (_22_150) -> begin
_22_150
end))

let ___Exp_constant____0 = (fun projectee -> (match (projectee) with
| Exp_constant (_22_153) -> begin
_22_153
end))

let ___Exp_abs____0 = (fun projectee -> (match (projectee) with
| Exp_abs (_22_156) -> begin
_22_156
end))

let ___Exp_app____0 = (fun projectee -> (match (projectee) with
| Exp_app (_22_159) -> begin
_22_159
end))

let ___Exp_match____0 = (fun projectee -> (match (projectee) with
| Exp_match (_22_162) -> begin
_22_162
end))

let ___Exp_ascribed____0 = (fun projectee -> (match (projectee) with
| Exp_ascribed (_22_165) -> begin
_22_165
end))

let ___Exp_let____0 = (fun projectee -> (match (projectee) with
| Exp_let (_22_168) -> begin
_22_168
end))

let ___Exp_uvar____0 = (fun projectee -> (match (projectee) with
| Exp_uvar (_22_171) -> begin
_22_171
end))

let ___Exp_delayed____0 = (fun projectee -> (match (projectee) with
| Exp_delayed (_22_174) -> begin
_22_174
end))

let ___Exp_meta____0 = (fun projectee -> (match (projectee) with
| Exp_meta (_22_177) -> begin
_22_177
end))

let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_22_179) -> begin
_22_179
end))

let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_22_182) -> begin
_22_182
end))

let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_22_185) -> begin
_22_185
end))

let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_22_188) -> begin
_22_188
end))

let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_22_191) -> begin
_22_191
end))

let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_22_194) -> begin
_22_194
end))

let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_22_197) -> begin
_22_197
end))

let ___Pat_tvar____0 = (fun projectee -> (match (projectee) with
| Pat_tvar (_22_200) -> begin
_22_200
end))

let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_22_203) -> begin
_22_203
end))

let ___Pat_twild____0 = (fun projectee -> (match (projectee) with
| Pat_twild (_22_206) -> begin
_22_206
end))

let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_22_209) -> begin
_22_209
end))

let ___Pat_dot_typ____0 = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_22_212) -> begin
_22_212
end))

let ___Kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Kind_abbrev (_22_215) -> begin
_22_215
end))

let ___Kind_arrow____0 = (fun projectee -> (match (projectee) with
| Kind_arrow (_22_218) -> begin
_22_218
end))

let ___Kind_uvar____0 = (fun projectee -> (match (projectee) with
| Kind_uvar (_22_221) -> begin
_22_221
end))

let ___Kind_lam____0 = (fun projectee -> (match (projectee) with
| Kind_lam (_22_224) -> begin
_22_224
end))

let ___Kind_delayed____0 = (fun projectee -> (match (projectee) with
| Kind_delayed (_22_227) -> begin
_22_227
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
| Discriminator (_22_234) -> begin
_22_234
end))

let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_22_237) -> begin
_22_237
end))

let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_22_240) -> begin
_22_240
end))

let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_22_243) -> begin
_22_243
end))

let ___DefaultEffect____0 = (fun projectee -> (match (projectee) with
| DefaultEffect (_22_246) -> begin
_22_246
end))

type tycon =
(lident * binders * knd)

type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

let is_Mkmonad_abbrev = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))

type sub_eff =
{source : lident; target : lident; lift : typ}

let is_Mksub_eff = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))

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

let is_Mkeff_decl = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))

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
| Sig_tycon (_22_276) -> begin
_22_276
end))

let ___Sig_kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_22_279) -> begin
_22_279
end))

let ___Sig_typ_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_22_282) -> begin
_22_282
end))

let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_22_285) -> begin
_22_285
end))

let ___Sig_val_decl____0 = (fun projectee -> (match (projectee) with
| Sig_val_decl (_22_288) -> begin
_22_288
end))

let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_22_291) -> begin
_22_291
end))

let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_22_294) -> begin
_22_294
end))

let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_22_297) -> begin
_22_297
end))

let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_22_300) -> begin
_22_300
end))

let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_22_303) -> begin
_22_303
end))

let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_22_306) -> begin
_22_306
end))

let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_22_309) -> begin
_22_309
end))

let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_22_312) -> begin
_22_312
end))

type sigelts =
sigelt Prims.list

type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}

let is_Mkmodul = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))

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
| K (_22_321) -> begin
_22_321
end))

let ___T____0 = (fun projectee -> (match (projectee) with
| T (_22_324) -> begin
_22_324
end))

let ___E____0 = (fun projectee -> (match (projectee) with
| E (_22_327) -> begin
_22_327
end))

let ___C____0 = (fun projectee -> (match (projectee) with
| C (_22_330) -> begin
_22_330
end))

type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

let is_Mklcomp = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))

type path =
Prims.string Prims.list

let dummyRange = 0L

let withinfo = (fun v s r -> {v = v; sort = s; p = r})

let withsort = (fun v s -> (withinfo v s dummyRange))

let mk_ident = (fun _22_343 -> (match (_22_343) with
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

let lid_of_ids = (fun ids -> (let _22_354 = (FStar_Util.prefix ids)
in (match (_22_354) with
| (ns, id) -> begin
(let nsstr = (let _88_1403 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _88_1403 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = (match ((nsstr = "")) with
| true -> begin
id.idText
end
| false -> begin
(Prims.strcat (Prims.strcat nsstr ".") id.idText)
end)})
end)))

let lid_of_path = (fun path pos -> (let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

let text_of_lid = (fun lid -> lid.str)

let lid_equals = (fun l1 l2 -> (l1.str = l2.str))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.idText = bvd2.realname.idText))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_22_369), FStar_Util.Inr (_22_372)) -> begin
(- (1))
end
| (FStar_Util.Inr (_22_376), FStar_Util.Inl (_22_379)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.idText y.realname.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.idText y.realname.idText)
end))

let lid_with_range = (fun lid r -> (let id = (let _22_394 = lid.ident
in {idText = _22_394.idText; idRange = r})
in (let _22_397 = lid
in {ns = _22_397.ns; ident = id; nsstr = _22_397.nsstr; str = _22_397.str})))

let range_of_lid = (fun lid -> lid.ident.idRange)

let range_of_lbname = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

let syn = (fun p k f -> (f k p))

let mk_fvs = (fun _22_408 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let mk_uvs = (fun _22_409 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

let new_ftv_set = (fun _22_410 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.idText y.v.realname.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.idText)))
end))

let new_uv_set = (fun _22_414 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

let new_uvt_set = (fun _22_417 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _22_425 _22_429 -> (match ((_22_425, _22_429)) with
| ((x, _22_424), (y, _22_428)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _22_421 -> (match (_22_421) with
| (x, _22_420) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

let no_fvs = (let _88_1452 = (new_ftv_set ())
in (let _88_1451 = (new_ftv_set ())
in {ftvs = _88_1452; fxvs = _88_1451}))

let no_uvs = (let _88_1455 = (new_uv_set ())
in (let _88_1454 = (new_uvt_set ())
in (let _88_1453 = (new_uvt_set ())
in {uvars_k = _88_1455; uvars_t = _88_1454; uvars_e = _88_1453})))

let memo_no_uvs = (FStar_Util.mk_ref (Some (no_uvs)))

let memo_no_fvs = (FStar_Util.mk_ref (Some (no_fvs)))

let freevars_of_list = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _22_1 -> (match (_22_1) with
| FStar_Util.Inl (btv) -> begin
(let _22_435 = out
in (let _88_1460 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _88_1460; fxvs = _22_435.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(let _22_439 = out
in (let _88_1461 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _22_439.ftvs; fxvs = _88_1461}))
end)) no_fvs)))

let list_of_freevars = (fun fvs -> (let _88_1469 = (let _88_1465 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _88_1465 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _88_1468 = (let _88_1467 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _88_1467 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _88_1469 _88_1468))))

let get_unit_ref = (fun _22_444 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (())))
in (let _22_446 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let mk_Kind_type = (let _88_1474 = (get_unit_ref ())
in (let _88_1473 = (mk_fvs ())
in (let _88_1472 = (mk_uvs ())
in {n = Kind_type; tk = _88_1474; pos = dummyRange; fvs = _88_1473; uvs = _88_1472})))

let mk_Kind_effect = (let _88_1477 = (get_unit_ref ())
in (let _88_1476 = (mk_fvs ())
in (let _88_1475 = (mk_uvs ())
in {n = Kind_effect; tk = _88_1477; pos = dummyRange; fvs = _88_1476; uvs = _88_1475})))

let mk_Kind_abbrev = (fun _22_450 p -> (match (_22_450) with
| (kabr, k) -> begin
(let _88_1484 = (get_unit_ref ())
in (let _88_1483 = (mk_fvs ())
in (let _88_1482 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _88_1484; pos = p; fvs = _88_1483; uvs = _88_1482})))
end))

let mk_Kind_arrow = (fun _22_454 p -> (match (_22_454) with
| (bs, k) -> begin
(let _88_1491 = (get_unit_ref ())
in (let _88_1490 = (mk_fvs ())
in (let _88_1489 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _88_1491; pos = p; fvs = _88_1490; uvs = _88_1489})))
end))

let mk_Kind_arrow' = (fun _22_458 p -> (match (_22_458) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _22_462 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _22_468 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

let mk_Kind_uvar = (fun uv p -> (let _88_1502 = (get_unit_ref ())
in (let _88_1501 = (mk_fvs ())
in (let _88_1500 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _88_1502; pos = p; fvs = _88_1501; uvs = _88_1500}))))

let mk_Kind_lam = (fun _22_473 p -> (match (_22_473) with
| (vs, k) -> begin
(let _88_1509 = (get_unit_ref ())
in (let _88_1508 = (mk_fvs ())
in (let _88_1507 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _88_1509; pos = p; fvs = _88_1508; uvs = _88_1507})))
end))

let mk_Kind_delayed = (fun _22_478 p -> (match (_22_478) with
| (k, s, m) -> begin
(let _88_1516 = (get_unit_ref ())
in (let _88_1515 = (mk_fvs ())
in (let _88_1514 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _88_1516; pos = p; fvs = _88_1515; uvs = _88_1514})))
end))

let mk_Kind_unknown = (let _88_1519 = (get_unit_ref ())
in (let _88_1518 = (mk_fvs ())
in (let _88_1517 = (mk_uvs ())
in {n = Kind_unknown; tk = _88_1519; pos = dummyRange; fvs = _88_1518; uvs = _88_1517})))

let get_knd_nref = (fun _22_480 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _22_482 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_knd_ref = (fun k -> (let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _22_486 = (FStar_ST.op_Colon_Equals x k)
in x)))

let mk_Typ_btvar = (fun x k p -> (let _88_1532 = (get_knd_ref k)
in (let _88_1531 = (mk_fvs ())
in (let _88_1530 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _88_1532; pos = p; fvs = _88_1531; uvs = _88_1530}))))

let mk_Typ_const = (fun x k p -> (let _88_1539 = (get_knd_ref k)
in {n = Typ_const (x); tk = _88_1539; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _22_499 -> begin
Typ_fun ((bs, c))
end))

let mk_Typ_fun = (fun _22_502 k p -> (match (_22_502) with
| (bs, c) -> begin
(let _88_1552 = (check_fun bs c p)
in (let _88_1551 = (FStar_Util.mk_ref k)
in (let _88_1550 = (mk_fvs ())
in (let _88_1549 = (mk_uvs ())
in {n = _88_1552; tk = _88_1551; pos = p; fvs = _88_1550; uvs = _88_1549}))))
end))

let mk_Typ_refine = (fun _22_507 k p -> (match (_22_507) with
| (x, phi) -> begin
(let _88_1561 = (FStar_Util.mk_ref k)
in (let _88_1560 = (mk_fvs ())
in (let _88_1559 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _88_1561; pos = p; fvs = _88_1560; uvs = _88_1559})))
end))

let mk_Typ_app = (fun _22_512 k p -> (match (_22_512) with
| (t1, args) -> begin
(let _88_1571 = (match (args) with
| [] -> begin
(FStar_All.failwith "Empty arg list!")
end
| _22_517 -> begin
Typ_app ((t1, args))
end)
in (let _88_1570 = (FStar_Util.mk_ref k)
in (let _88_1569 = (mk_fvs ())
in (let _88_1568 = (mk_uvs ())
in {n = _88_1571; tk = _88_1570; pos = p; fvs = _88_1569; uvs = _88_1568}))))
end))

let mk_Typ_app' = (fun _22_520 k p -> (match (_22_520) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _22_525 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

let extend_typ_app = (fun _22_528 k p -> (match (_22_528) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _22_536 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

let mk_Typ_lam = (fun _22_539 k p -> (match (_22_539) with
| (b, t) -> begin
(let _88_1593 = (match (b) with
| [] -> begin
(FStar_All.failwith "Empty binders!")
end
| _22_544 -> begin
Typ_lam ((b, t))
end)
in (let _88_1592 = (FStar_Util.mk_ref k)
in (let _88_1591 = (mk_fvs ())
in (let _88_1590 = (mk_uvs ())
in {n = _88_1593; tk = _88_1592; pos = p; fvs = _88_1591; uvs = _88_1590}))))
end))

let mk_Typ_lam' = (fun _22_547 k p -> (match (_22_547) with
| (bs, t) -> begin
(match (bs) with
| [] -> begin
t
end
| _22_552 -> begin
(mk_Typ_lam (bs, t) k p)
end)
end))

let mk_Typ_ascribed' = (fun _22_555 k' p -> (match (_22_555) with
| (t, k) -> begin
(let _88_1608 = (FStar_Util.mk_ref k')
in (let _88_1607 = (mk_fvs ())
in (let _88_1606 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _88_1608; pos = p; fvs = _88_1607; uvs = _88_1606})))
end))

let mk_Typ_ascribed = (fun _22_560 p -> (match (_22_560) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

let mk_Typ_meta' = (fun m k p -> (let _88_1621 = (FStar_Util.mk_ref k)
in (let _88_1620 = (mk_fvs ())
in (let _88_1619 = (mk_uvs ())
in {n = Typ_meta (m); tk = _88_1621; pos = p; fvs = _88_1620; uvs = _88_1619}))))

let mk_Typ_meta = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _88_1624 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _88_1624 t.pos))
end))

let mk_Typ_uvar' = (fun _22_597 k' p -> (match (_22_597) with
| (u, k) -> begin
(let _88_1633 = (get_knd_ref k')
in (let _88_1632 = (mk_fvs ())
in (let _88_1631 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _88_1633; pos = p; fvs = _88_1632; uvs = _88_1631})))
end))

let mk_Typ_uvar = (fun _22_602 p -> (match (_22_602) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

let mk_Typ_delayed = (fun _22_607 k p -> (match (_22_607) with
| (t, s, m) -> begin
(let _88_1653 = (match (t.n) with
| Typ_delayed (_22_611) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _22_614 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _88_1652 = (FStar_Util.mk_ref k)
in (let _88_1651 = (mk_fvs ())
in (let _88_1650 = (mk_uvs ())
in {n = _88_1653; tk = _88_1652; pos = p; fvs = _88_1651; uvs = _88_1650}))))
end))

let mk_Typ_delayed' = (fun st k p -> (let _88_1675 = (let _88_1671 = (let _88_1670 = (FStar_Util.mk_ref None)
in (st, _88_1670))
in Typ_delayed (_88_1671))
in (let _88_1674 = (FStar_Util.mk_ref k)
in (let _88_1673 = (mk_fvs ())
in (let _88_1672 = (mk_uvs ())
in {n = _88_1675; tk = _88_1674; pos = p; fvs = _88_1673; uvs = _88_1672})))))

let mk_Typ_unknown = (let _88_1678 = (get_knd_nref ())
in (let _88_1677 = (mk_fvs ())
in (let _88_1676 = (mk_uvs ())
in {n = Typ_unknown; tk = _88_1678; pos = dummyRange; fvs = _88_1677; uvs = _88_1676})))

let get_typ_nref = (fun _22_618 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _22_620 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

let get_typ_ref = (fun t -> (let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _22_624 = (FStar_ST.op_Colon_Equals x t)
in x)))

let mk_Total = (fun t -> (let _88_1687 = (FStar_Util.mk_ref None)
in (let _88_1686 = (mk_fvs ())
in (let _88_1685 = (mk_uvs ())
in {n = Total (t); tk = _88_1687; pos = t.pos; fvs = _88_1686; uvs = _88_1685}))))

let mk_Comp = (fun ct -> (let _88_1692 = (FStar_Util.mk_ref None)
in (let _88_1691 = (mk_fvs ())
in (let _88_1690 = (mk_uvs ())
in {n = Comp (ct); tk = _88_1692; pos = ct.result_typ.pos; fvs = _88_1691; uvs = _88_1690}))))

let mk_Exp_bvar = (fun x t p -> (let _88_1701 = (get_typ_ref t)
in (let _88_1700 = (mk_fvs ())
in (let _88_1699 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _88_1701; pos = p; fvs = _88_1700; uvs = _88_1699}))))

let mk_Exp_fvar = (fun _22_633 t p -> (match (_22_633) with
| (x, b) -> begin
(let _88_1710 = (get_typ_ref t)
in (let _88_1709 = (mk_fvs ())
in (let _88_1708 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _88_1710; pos = p; fvs = _88_1709; uvs = _88_1708})))
end))

let mk_Exp_constant = (fun s t p -> (let _88_1719 = (get_typ_ref t)
in (let _88_1718 = (mk_fvs ())
in (let _88_1717 = (mk_uvs ())
in {n = Exp_constant (s); tk = _88_1719; pos = p; fvs = _88_1718; uvs = _88_1717}))))

let mk_Exp_abs = (fun _22_641 t' p -> (match (_22_641) with
| (b, e) -> begin
(let _88_1729 = (match (b) with
| [] -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _22_646 -> begin
Exp_abs ((b, e))
end)
in (let _88_1728 = (get_typ_ref t')
in (let _88_1727 = (mk_fvs ())
in (let _88_1726 = (mk_uvs ())
in {n = _88_1729; tk = _88_1728; pos = p; fvs = _88_1727; uvs = _88_1726}))))
end))

let mk_Exp_abs' = (fun _22_649 t' p -> (match (_22_649) with
| (b, e) -> begin
(let _88_1739 = (match ((b, e.n)) with
| (_22_653, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _22_663) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _22_666 -> begin
Exp_abs ((b, e))
end)
in (let _88_1738 = (get_typ_ref t')
in (let _88_1737 = (mk_fvs ())
in (let _88_1736 = (mk_uvs ())
in {n = _88_1739; tk = _88_1738; pos = p; fvs = _88_1737; uvs = _88_1736}))))
end))

let mk_Exp_app = (fun _22_669 t p -> (match (_22_669) with
| (e1, args) -> begin
(let _88_1749 = (match (args) with
| [] -> begin
(FStar_All.failwith "Empty args!")
end
| _22_674 -> begin
Exp_app ((e1, args))
end)
in (let _88_1748 = (get_typ_ref t)
in (let _88_1747 = (mk_fvs ())
in (let _88_1746 = (mk_uvs ())
in {n = _88_1749; tk = _88_1748; pos = p; fvs = _88_1747; uvs = _88_1746}))))
end))

let mk_Exp_app_flat = (fun _22_677 t p -> (match (_22_677) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _22_685 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let mk_Exp_app' = (fun _22_688 t p -> (match (_22_688) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _22_693 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let rec pat_vars = (fun p -> (match (p.v) with
| Pat_cons (_22_696, _22_698, ps) -> begin
(let vars = (FStar_List.collect (fun _22_705 -> (match (_22_705) with
| (x, _22_704) -> begin
(pat_vars x)
end)) ps)
in (match ((FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _22_720 -> begin
false
end))))) with
| true -> begin
vars
end
| false -> begin
(Prims.raise (Error (("Pattern variables may not occur more than once", p.p))))
end))
end
| Pat_var (x) -> begin
(FStar_Util.Inr (x.v))::[]
end
| Pat_tvar (a) -> begin
(FStar_Util.Inl (a.v))::[]
end
| Pat_disj (ps) -> begin
(let vars = (FStar_List.map pat_vars ps)
in (match ((not ((let _88_1770 = (FStar_List.tl vars)
in (let _88_1769 = (let _88_1768 = (let _88_1767 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _88_1767))
in (FStar_Util.for_all _88_1768))
in (FStar_All.pipe_right _88_1770 _88_1769)))))) with
| true -> begin
(let vars = (let _88_1774 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _88_1773 = (FStar_List.map (fun _22_2 -> (match (_22_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.idText
end)) v)
in (FStar_Util.concat_l ", " _88_1773)))))
in (FStar_Util.concat_l ";\n" _88_1774))
in (let _88_1777 = (let _88_1776 = (let _88_1775 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_88_1775, p.p))
in Error (_88_1776))
in (Prims.raise _88_1777)))
end
| false -> begin
(FStar_List.hd vars)
end))
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

let mk_Exp_match = (fun _22_752 t p -> (match (_22_752) with
| (e, pats) -> begin
(let _88_1786 = (get_typ_ref t)
in (let _88_1785 = (mk_fvs ())
in (let _88_1784 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _88_1786; pos = p; fvs = _88_1785; uvs = _88_1784})))
end))

let mk_Exp_ascribed = (fun _22_758 t' p -> (match (_22_758) with
| (e, t, l) -> begin
(let _88_1795 = (get_typ_ref t')
in (let _88_1794 = (mk_fvs ())
in (let _88_1793 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _88_1795; pos = p; fvs = _88_1794; uvs = _88_1793})))
end))

let mk_Exp_let = (fun _22_763 t p -> (match (_22_763) with
| (lbs, e) -> begin
(let _88_1804 = (get_typ_ref t)
in (let _88_1803 = (mk_fvs ())
in (let _88_1802 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _88_1804; pos = p; fvs = _88_1803; uvs = _88_1802})))
end))

let mk_Exp_uvar' = (fun _22_768 t' p -> (match (_22_768) with
| (u, t) -> begin
(let _88_1813 = (get_typ_ref t')
in (let _88_1812 = (mk_fvs ())
in (let _88_1811 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _88_1813; pos = p; fvs = _88_1812; uvs = _88_1811})))
end))

let mk_Exp_uvar = (fun _22_773 p -> (match (_22_773) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

let mk_Exp_delayed = (fun _22_778 t p -> (match (_22_778) with
| (e, s, m) -> begin
(let _88_1826 = (get_typ_ref t)
in (let _88_1825 = (mk_fvs ())
in (let _88_1824 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _88_1826; pos = p; fvs = _88_1825; uvs = _88_1824})))
end))

let mk_Exp_meta' = (fun m t p -> (let _88_1835 = (get_typ_ref t)
in (let _88_1834 = (mk_fvs ())
in (let _88_1833 = (mk_uvs ())
in {n = Exp_meta (m); tk = _88_1835; pos = p; fvs = _88_1834; uvs = _88_1833}))))

let mk_Exp_meta = (fun m -> (match (m) with
| Meta_desugared (e, _22_787) -> begin
(let _88_1838 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _88_1838 e.pos))
end))

let mk_lb = (fun _22_794 -> (match (_22_794) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst = (fun s -> s)

let extend_subst = (fun x s -> (x)::s)

let argpos = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _22_802) -> begin
t.pos
end
| (FStar_Util.Inr (e), _22_807) -> begin
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

let null_t_binder = (fun t -> (let _88_1857 = (let _88_1856 = (null_bvar t)
in FStar_Util.Inl (_88_1856))
in (_88_1857, None)))

let null_v_binder = (fun t -> (let _88_1861 = (let _88_1860 = (null_bvar t)
in FStar_Util.Inr (_88_1860))
in (_88_1861, None)))

let itarg = (fun t -> (FStar_Util.Inl (t), Some (Implicit)))

let ivarg = (fun v -> (FStar_Util.Inr (v), Some (Implicit)))

let targ = (fun t -> (FStar_Util.Inl (t), None))

let varg = (fun v -> (FStar_Util.Inr (v), None))

let is_null_pp = (fun b -> (b.ppname.idText = null_id.idText))

let is_null_bvd = (fun b -> (b.realname.idText = null_id.idText))

let is_null_bvar = (fun b -> (is_null_bvd b.v))

let is_null_binder = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _22_829) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _22_834) -> begin
(is_null_bvar x)
end))

let freevars_of_binders = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _22_3 -> (match (_22_3) with
| (FStar_Util.Inl (btv), _22_842) -> begin
(let _22_844 = out
in (let _88_1882 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _88_1882; fxvs = _22_844.fxvs}))
end
| (FStar_Util.Inr (bxv), _22_849) -> begin
(let _22_851 = out
in (let _88_1883 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _22_851.ftvs; fxvs = _88_1883}))
end)) no_fvs)))

let binders_of_list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

let binders_of_freevars = (fun fvs -> (let _88_1892 = (let _88_1889 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _88_1889 (FStar_List.map t_binder)))
in (let _88_1891 = (let _88_1890 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _88_1890 (FStar_List.map v_binder)))
in (FStar_List.append _88_1892 _88_1891))))

let is_implicit = (fun _22_4 -> (match (_22_4) with
| Some (Implicit) -> begin
true
end
| _22_860 -> begin
false
end))

let as_implicit = (fun _22_5 -> (match (_22_5) with
| true -> begin
Some (Implicit)
end
| _22_864 -> begin
None
end))




