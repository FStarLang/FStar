
open Prims
# 26 "syntax.fs"

type ident =
FStar_Ident.ident

# 27 "syntax.fs"

type lident =
FStar_Ident.lid

# 28 "syntax.fs"

type l__LongIdent =
lident

# 29 "syntax.fs"

exception Err of (Prims.string)

# 29 "syntax.fs"

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "syntax.fs"

let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_25_7) -> begin
_25_7
end))

# 30 "syntax.fs"

exception Error of ((Prims.string * FStar_Range.range))

# 30 "syntax.fs"

let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "syntax.fs"

let ___Error____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (_25_9) -> begin
_25_9
end))

# 31 "syntax.fs"

exception Warning of ((Prims.string * FStar_Range.range))

# 31 "syntax.fs"

let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "syntax.fs"

let ___Warning____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (_25_11) -> begin
_25_11
end))

# 33 "syntax.fs"

type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}

# 33 "syntax.fs"

let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

# 38 "syntax.fs"

type 't var =
(lident, 't) withinfo_t

# 39 "syntax.fs"

type fieldname =
lident

# 40 "syntax.fs"

type 'a bvdef =
{ppname : ident; realname : ident}

# 40 "syntax.fs"

let is_Mkbvdef = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbvdef"))))

# 41 "syntax.fs"

type ('a, 't) bvar =
('a bvdef, 't) withinfo_t

# 47 "syntax.fs"

type sconst =
FStar_Const.sconst

# 48 "syntax.fs"

type pragma =
| SetOptions of Prims.string
| ResetOptions

# 49 "syntax.fs"

let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "syntax.fs"

let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "syntax.fs"

let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_25_27) -> begin
_25_27
end))

# 51 "syntax.fs"

type 'a memo =
'a Prims.option FStar_ST.ref

# 52 "syntax.fs"

type arg_qualifier =
| Implicit of Prims.bool
| Equality

# 53 "syntax.fs"

let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "syntax.fs"

let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "syntax.fs"

let ___Implicit____0 : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_25_31) -> begin
_25_31
end))

# 55 "syntax.fs"

type aqual =
arg_qualifier Prims.option

# 56 "syntax.fs"

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

# 57 "syntax.fs"

let is_Typ_btvar = (fun _discr_ -> (match (_discr_) with
| Typ_btvar (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "syntax.fs"

let is_Typ_const = (fun _discr_ -> (match (_discr_) with
| Typ_const (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "syntax.fs"

let is_Typ_fun = (fun _discr_ -> (match (_discr_) with
| Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "syntax.fs"

let is_Typ_refine = (fun _discr_ -> (match (_discr_) with
| Typ_refine (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "syntax.fs"

let is_Typ_app = (fun _discr_ -> (match (_discr_) with
| Typ_app (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "syntax.fs"

let is_Typ_lam = (fun _discr_ -> (match (_discr_) with
| Typ_lam (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "syntax.fs"

let is_Typ_ascribed = (fun _discr_ -> (match (_discr_) with
| Typ_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "syntax.fs"

let is_Typ_meta = (fun _discr_ -> (match (_discr_) with
| Typ_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "syntax.fs"

let is_Typ_uvar = (fun _discr_ -> (match (_discr_) with
| Typ_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "syntax.fs"

let is_Typ_delayed = (fun _discr_ -> (match (_discr_) with
| Typ_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "syntax.fs"

let is_Typ_unknown = (fun _discr_ -> (match (_discr_) with
| Typ_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "syntax.fs"

let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

# 80 "syntax.fs"

let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "syntax.fs"

let is_Comp = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "syntax.fs"

let is_TOTAL = (fun _discr_ -> (match (_discr_) with
| TOTAL (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "syntax.fs"

let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "syntax.fs"

let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "syntax.fs"

let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "syntax.fs"

let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "syntax.fs"

let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "syntax.fs"

let is_DECREASES = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "syntax.fs"

let is_Meta_pattern = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "syntax.fs"

let is_Meta_named = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "syntax.fs"

let is_Meta_labeled = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 96 "syntax.fs"

let is_Meta_refresh_label = (fun _discr_ -> (match (_discr_) with
| Meta_refresh_label (_) -> begin
true
end
| _ -> begin
false
end))

# 97 "syntax.fs"

let is_Meta_slack_formula = (fun _discr_ -> (match (_discr_) with
| Meta_slack_formula (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "syntax.fs"

let is_Uvar = (fun _ _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 100 "syntax.fs"

let is_Fixed = (fun _ _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "syntax.fs"

let is_Exp_bvar = (fun _discr_ -> (match (_discr_) with
| Exp_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "syntax.fs"

let is_Exp_fvar = (fun _discr_ -> (match (_discr_) with
| Exp_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "syntax.fs"

let is_Exp_constant = (fun _discr_ -> (match (_discr_) with
| Exp_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "syntax.fs"

let is_Exp_abs = (fun _discr_ -> (match (_discr_) with
| Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "syntax.fs"

let is_Exp_app = (fun _discr_ -> (match (_discr_) with
| Exp_app (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "syntax.fs"

let is_Exp_match = (fun _discr_ -> (match (_discr_) with
| Exp_match (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "syntax.fs"

let is_Exp_ascribed = (fun _discr_ -> (match (_discr_) with
| Exp_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "syntax.fs"

let is_Exp_let = (fun _discr_ -> (match (_discr_) with
| Exp_let (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "syntax.fs"

let is_Exp_uvar = (fun _discr_ -> (match (_discr_) with
| Exp_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "syntax.fs"

let is_Exp_delayed = (fun _discr_ -> (match (_discr_) with
| Exp_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "syntax.fs"

let is_Exp_meta = (fun _discr_ -> (match (_discr_) with
| Exp_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 115 "syntax.fs"

let is_Meta_desugared = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

# 117 "syntax.fs"

let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "syntax.fs"

let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "syntax.fs"

let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop (_) -> begin
true
end
| _ -> begin
false
end))

# 120 "syntax.fs"

let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "syntax.fs"

let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "syntax.fs"

let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 124 "syntax.fs"

let is_Record_projector = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

# 125 "syntax.fs"

let is_Record_ctor = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 130 "syntax.fs"

let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

# 131 "syntax.fs"

let is_Pat_constant = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "syntax.fs"

let is_Pat_cons = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "syntax.fs"

let is_Pat_var = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "syntax.fs"

let is_Pat_tvar = (fun _discr_ -> (match (_discr_) with
| Pat_tvar (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "syntax.fs"

let is_Pat_wild = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "syntax.fs"

let is_Pat_twild = (fun _discr_ -> (match (_discr_) with
| Pat_twild (_) -> begin
true
end
| _ -> begin
false
end))

# 137 "syntax.fs"

let is_Pat_dot_term = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

# 138 "syntax.fs"

let is_Pat_dot_typ = (fun _discr_ -> (match (_discr_) with
| Pat_dot_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "syntax.fs"

let is_Kind_type = (fun _discr_ -> (match (_discr_) with
| Kind_type (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "syntax.fs"

let is_Kind_effect = (fun _discr_ -> (match (_discr_) with
| Kind_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "syntax.fs"

let is_Kind_abbrev = (fun _discr_ -> (match (_discr_) with
| Kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 144 "syntax.fs"

let is_Kind_arrow = (fun _discr_ -> (match (_discr_) with
| Kind_arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "syntax.fs"

let is_Kind_uvar = (fun _discr_ -> (match (_discr_) with
| Kind_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "syntax.fs"

let is_Kind_lam = (fun _discr_ -> (match (_discr_) with
| Kind_lam (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "syntax.fs"

let is_Kind_delayed = (fun _discr_ -> (match (_discr_) with
| Kind_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 148 "syntax.fs"

let is_Kind_unknown = (fun _discr_ -> (match (_discr_) with
| Kind_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 154 "syntax.fs"

let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

# 165 "syntax.fs"

let is_Mkfreevars : freevars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfreevars"))))

# 169 "syntax.fs"

let is_Mkuvars : uvars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkuvars"))))

# 174 "syntax.fs"

let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

# 57 "syntax.fs"

let ___Typ_btvar____0 : typ'  ->  btvar = (fun projectee -> (match (projectee) with
| Typ_btvar (_25_55) -> begin
_25_55
end))

# 58 "syntax.fs"

let ___Typ_const____0 : typ'  ->  ftvar = (fun projectee -> (match (projectee) with
| Typ_const (_25_58) -> begin
_25_58
end))

# 59 "syntax.fs"

let ___Typ_fun____0 : typ'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Typ_fun (_25_61) -> begin
_25_61
end))

# 60 "syntax.fs"

let ___Typ_refine____0 : typ'  ->  (bvvar * typ) = (fun projectee -> (match (projectee) with
| Typ_refine (_25_64) -> begin
_25_64
end))

# 61 "syntax.fs"

let ___Typ_app____0 : typ'  ->  (typ * args) = (fun projectee -> (match (projectee) with
| Typ_app (_25_67) -> begin
_25_67
end))

# 62 "syntax.fs"

let ___Typ_lam____0 : typ'  ->  (binders * typ) = (fun projectee -> (match (projectee) with
| Typ_lam (_25_70) -> begin
_25_70
end))

# 63 "syntax.fs"

let ___Typ_ascribed____0 : typ'  ->  (typ * knd) = (fun projectee -> (match (projectee) with
| Typ_ascribed (_25_73) -> begin
_25_73
end))

# 64 "syntax.fs"

let ___Typ_meta____0 : typ'  ->  meta_t = (fun projectee -> (match (projectee) with
| Typ_meta (_25_76) -> begin
_25_76
end))

# 65 "syntax.fs"

let ___Typ_uvar____0 : typ'  ->  (uvar_t * knd) = (fun projectee -> (match (projectee) with
| Typ_uvar (_25_79) -> begin
_25_79
end))

# 66 "syntax.fs"

let ___Typ_delayed____0 : typ'  ->  (((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either * typ memo) = (fun projectee -> (match (projectee) with
| Typ_delayed (_25_82) -> begin
_25_82
end))

# 80 "syntax.fs"

let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_25_86) -> begin
_25_86
end))

# 81 "syntax.fs"

let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_25_89) -> begin
_25_89
end))

# 90 "syntax.fs"

let ___DECREASES____0 : cflags  ->  exp = (fun projectee -> (match (projectee) with
| DECREASES (_25_92) -> begin
_25_92
end))

# 93 "syntax.fs"

let ___Meta_pattern____0 : meta_t  ->  (typ * arg Prims.list Prims.list) = (fun projectee -> (match (projectee) with
| Meta_pattern (_25_95) -> begin
_25_95
end))

# 94 "syntax.fs"

let ___Meta_named____0 : meta_t  ->  (typ * lident) = (fun projectee -> (match (projectee) with
| Meta_named (_25_98) -> begin
_25_98
end))

# 95 "syntax.fs"

let ___Meta_labeled____0 : meta_t  ->  (typ * Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_25_101) -> begin
_25_101
end))

# 96 "syntax.fs"

let ___Meta_refresh_label____0 : meta_t  ->  (typ * Prims.bool Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_25_104) -> begin
_25_104
end))

# 97 "syntax.fs"

let ___Meta_slack_formula____0 : meta_t  ->  (typ * typ * Prims.bool FStar_ST.ref) = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_25_107) -> begin
_25_107
end))

# 100 "syntax.fs"

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_25_110) -> begin
_25_110
end))

# 102 "syntax.fs"

let ___Exp_bvar____0 : exp'  ->  bvvar = (fun projectee -> (match (projectee) with
| Exp_bvar (_25_113) -> begin
_25_113
end))

# 103 "syntax.fs"

let ___Exp_fvar____0 : exp'  ->  (fvvar * fv_qual Prims.option) = (fun projectee -> (match (projectee) with
| Exp_fvar (_25_116) -> begin
_25_116
end))

# 104 "syntax.fs"

let ___Exp_constant____0 : exp'  ->  sconst = (fun projectee -> (match (projectee) with
| Exp_constant (_25_119) -> begin
_25_119
end))

# 105 "syntax.fs"

let ___Exp_abs____0 : exp'  ->  (binders * exp) = (fun projectee -> (match (projectee) with
| Exp_abs (_25_122) -> begin
_25_122
end))

# 106 "syntax.fs"

let ___Exp_app____0 : exp'  ->  (exp * args) = (fun projectee -> (match (projectee) with
| Exp_app (_25_125) -> begin
_25_125
end))

# 107 "syntax.fs"

let ___Exp_match____0 : exp'  ->  (exp * (pat * exp Prims.option * exp) Prims.list) = (fun projectee -> (match (projectee) with
| Exp_match (_25_128) -> begin
_25_128
end))

# 108 "syntax.fs"

let ___Exp_ascribed____0 : exp'  ->  (exp * typ * lident Prims.option) = (fun projectee -> (match (projectee) with
| Exp_ascribed (_25_131) -> begin
_25_131
end))

# 109 "syntax.fs"

let ___Exp_let____0 : exp'  ->  (letbindings * exp) = (fun projectee -> (match (projectee) with
| Exp_let (_25_134) -> begin
_25_134
end))

# 110 "syntax.fs"

let ___Exp_uvar____0 : exp'  ->  (uvar_e * typ) = (fun projectee -> (match (projectee) with
| Exp_uvar (_25_137) -> begin
_25_137
end))

# 111 "syntax.fs"

let ___Exp_delayed____0 : exp'  ->  (exp * subst_t * exp memo) = (fun projectee -> (match (projectee) with
| Exp_delayed (_25_140) -> begin
_25_140
end))

# 112 "syntax.fs"

let ___Exp_meta____0 : exp'  ->  meta_e = (fun projectee -> (match (projectee) with
| Exp_meta (_25_143) -> begin
_25_143
end))

# 115 "syntax.fs"

let ___Meta_desugared____0 : meta_e  ->  (exp * meta_source_info) = (fun projectee -> (match (projectee) with
| Meta_desugared (_25_145) -> begin
_25_145
end))

# 124 "syntax.fs"

let ___Record_projector____0 : fv_qual  ->  lident = (fun projectee -> (match (projectee) with
| Record_projector (_25_148) -> begin
_25_148
end))

# 125 "syntax.fs"

let ___Record_ctor____0 : fv_qual  ->  (lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_25_151) -> begin
_25_151
end))

# 130 "syntax.fs"

let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_25_154) -> begin
_25_154
end))

# 131 "syntax.fs"

let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_25_157) -> begin
_25_157
end))

# 132 "syntax.fs"

let ___Pat_cons____0 : pat'  ->  (fvvar * fv_qual Prims.option * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_25_160) -> begin
_25_160
end))

# 133 "syntax.fs"

let ___Pat_var____0 : pat'  ->  bvvar = (fun projectee -> (match (projectee) with
| Pat_var (_25_163) -> begin
_25_163
end))

# 134 "syntax.fs"

let ___Pat_tvar____0 : pat'  ->  btvar = (fun projectee -> (match (projectee) with
| Pat_tvar (_25_166) -> begin
_25_166
end))

# 135 "syntax.fs"

let ___Pat_wild____0 : pat'  ->  bvvar = (fun projectee -> (match (projectee) with
| Pat_wild (_25_169) -> begin
_25_169
end))

# 136 "syntax.fs"

let ___Pat_twild____0 : pat'  ->  btvar = (fun projectee -> (match (projectee) with
| Pat_twild (_25_172) -> begin
_25_172
end))

# 137 "syntax.fs"

let ___Pat_dot_term____0 : pat'  ->  (bvvar * exp) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_25_175) -> begin
_25_175
end))

# 138 "syntax.fs"

let ___Pat_dot_typ____0 : pat'  ->  (btvar * typ) = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_25_178) -> begin
_25_178
end))

# 143 "syntax.fs"

let ___Kind_abbrev____0 : knd'  ->  (kabbrev * knd) = (fun projectee -> (match (projectee) with
| Kind_abbrev (_25_181) -> begin
_25_181
end))

# 144 "syntax.fs"

let ___Kind_arrow____0 : knd'  ->  (binders * knd) = (fun projectee -> (match (projectee) with
| Kind_arrow (_25_184) -> begin
_25_184
end))

# 145 "syntax.fs"

let ___Kind_uvar____0 : knd'  ->  uvar_k_app = (fun projectee -> (match (projectee) with
| Kind_uvar (_25_187) -> begin
_25_187
end))

# 146 "syntax.fs"

let ___Kind_lam____0 : knd'  ->  (binders * knd) = (fun projectee -> (match (projectee) with
| Kind_lam (_25_190) -> begin
_25_190
end))

# 147 "syntax.fs"

let ___Kind_delayed____0 : knd'  ->  (knd * subst_t * knd memo) = (fun projectee -> (match (projectee) with
| Kind_delayed (_25_193) -> begin
_25_193
end))

# 186 "syntax.fs"

type subst =
subst_elt Prims.list

# 187 "syntax.fs"

type either_var =
(btvar, bvvar) FStar_Util.either

# 188 "syntax.fs"

type freevars_l =
either_var Prims.list

# 189 "syntax.fs"

type formula =
typ

# 190 "syntax.fs"

type formulae =
typ Prims.list

# 191 "syntax.fs"

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

# 192 "syntax.fs"

let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 193 "syntax.fs"

let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 194 "syntax.fs"

let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque (_) -> begin
true
end
| _ -> begin
false
end))

# 195 "syntax.fs"

let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 196 "syntax.fs"

let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 197 "syntax.fs"

let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 198 "syntax.fs"

let is_Discriminator = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

# 199 "syntax.fs"

let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

# 200 "syntax.fs"

let is_RecordType = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

# 201 "syntax.fs"

let is_RecordConstructor = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 202 "syntax.fs"

let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 203 "syntax.fs"

let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 204 "syntax.fs"

let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 205 "syntax.fs"

let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 206 "syntax.fs"

let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 198 "syntax.fs"

let ___Discriminator____0 : qualifier  ->  lident = (fun projectee -> (match (projectee) with
| Discriminator (_25_200) -> begin
_25_200
end))

# 199 "syntax.fs"

let ___Projector____0 : qualifier  ->  (lident * (btvdef, bvvdef) FStar_Util.either) = (fun projectee -> (match (projectee) with
| Projector (_25_203) -> begin
_25_203
end))

# 200 "syntax.fs"

let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_25_206) -> begin
_25_206
end))

# 201 "syntax.fs"

let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_25_209) -> begin
_25_209
end))

# 203 "syntax.fs"

let ___DefaultEffect____0 : qualifier  ->  lident Prims.option = (fun projectee -> (match (projectee) with
| DefaultEffect (_25_212) -> begin
_25_212
end))

# 208 "syntax.fs"

type tycon =
(lident * binders * knd)

# 209 "syntax.fs"

type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

# 209 "syntax.fs"

let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

# 214 "syntax.fs"

type sub_eff =
{source : lident; target : lident; lift : typ}

# 214 "syntax.fs"

let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

# 219 "syntax.fs"

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

# 219 "syntax.fs"

let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

# 240 "syntax.fs"

let is_Sig_tycon = (fun _discr_ -> (match (_discr_) with
| Sig_tycon (_) -> begin
true
end
| _ -> begin
false
end))

# 241 "syntax.fs"

let is_Sig_kind_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 242 "syntax.fs"

let is_Sig_typ_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_typ_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 243 "syntax.fs"

let is_Sig_datacon = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

# 244 "syntax.fs"

let is_Sig_val_decl = (fun _discr_ -> (match (_discr_) with
| Sig_val_decl (_) -> begin
true
end
| _ -> begin
false
end))

# 245 "syntax.fs"

let is_Sig_assume = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

# 246 "syntax.fs"

let is_Sig_let = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

# 247 "syntax.fs"

let is_Sig_main = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

# 248 "syntax.fs"

let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

# 249 "syntax.fs"

let is_Sig_new_effect = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 250 "syntax.fs"

let is_Sig_sub_effect = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 251 "syntax.fs"

let is_Sig_effect_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 252 "syntax.fs"

let is_Sig_pragma = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 240 "syntax.fs"

let ___Sig_tycon____0 : sigelt  ->  (lident * binders * knd * lident Prims.list * lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_tycon (_25_242) -> begin
_25_242
end))

# 241 "syntax.fs"

let ___Sig_kind_abbrev____0 : sigelt  ->  (lident * binders * knd * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_25_245) -> begin
_25_245
end))

# 242 "syntax.fs"

let ___Sig_typ_abbrev____0 : sigelt  ->  (lident * binders * knd * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_25_248) -> begin
_25_248
end))

# 243 "syntax.fs"

let ___Sig_datacon____0 : sigelt  ->  (lident * typ * tycon * qualifier Prims.list * lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_25_251) -> begin
_25_251
end))

# 244 "syntax.fs"

let ___Sig_val_decl____0 : sigelt  ->  (lident * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_val_decl (_25_254) -> begin
_25_254
end))

# 245 "syntax.fs"

let ___Sig_assume____0 : sigelt  ->  (lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_25_257) -> begin
_25_257
end))

# 246 "syntax.fs"

let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_25_260) -> begin
_25_260
end))

# 247 "syntax.fs"

let ___Sig_main____0 : sigelt  ->  (exp * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_25_263) -> begin
_25_263
end))

# 248 "syntax.fs"

let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_25_266) -> begin
_25_266
end))

# 249 "syntax.fs"

let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_25_269) -> begin
_25_269
end))

# 250 "syntax.fs"

let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_25_272) -> begin
_25_272
end))

# 251 "syntax.fs"

let ___Sig_effect_abbrev____0 : sigelt  ->  (lident * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_25_275) -> begin
_25_275
end))

# 252 "syntax.fs"

let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_25_278) -> begin
_25_278
end))

# 253 "syntax.fs"

type sigelts =
sigelt Prims.list

# 255 "syntax.fs"

type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}

# 255 "syntax.fs"

let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

# 263 "syntax.fs"

type ktec =
| K of knd
| T of (typ * knd Prims.option)
| E of exp
| C of comp

# 264 "syntax.fs"

let is_K = (fun _discr_ -> (match (_discr_) with
| K (_) -> begin
true
end
| _ -> begin
false
end))

# 265 "syntax.fs"

let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 266 "syntax.fs"

let is_E = (fun _discr_ -> (match (_discr_) with
| E (_) -> begin
true
end
| _ -> begin
false
end))

# 267 "syntax.fs"

let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 264 "syntax.fs"

let ___K____0 : ktec  ->  knd = (fun projectee -> (match (projectee) with
| K (_25_287) -> begin
_25_287
end))

# 265 "syntax.fs"

let ___T____0 : ktec  ->  (typ * knd Prims.option) = (fun projectee -> (match (projectee) with
| T (_25_290) -> begin
_25_290
end))

# 266 "syntax.fs"

let ___E____0 : ktec  ->  exp = (fun projectee -> (match (projectee) with
| E (_25_293) -> begin
_25_293
end))

# 267 "syntax.fs"

let ___C____0 : ktec  ->  comp = (fun projectee -> (match (projectee) with
| C (_25_296) -> begin
_25_296
end))

# 269 "syntax.fs"

type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

# 269 "syntax.fs"

let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

# 279 "syntax.fs"

type path =
Prims.string Prims.list

# 280 "syntax.fs"

let dummyRange : Prims.int64 = 0L

# 281 "syntax.fs"

let withinfo = (fun v s r -> {v = v; sort = s; p = r})

# 282 "syntax.fs"

let withsort = (fun v s -> (withinfo v s dummyRange))

# 283 "syntax.fs"

let mk_ident : (Prims.string * FStar_Range.range)  ->  FStar_Ident.ident = (fun _25_309 -> (match (_25_309) with
| (text, range) -> begin
{FStar_Ident.idText = text; FStar_Ident.idRange = range}
end))

# 284 "syntax.fs"

let id_of_text : Prims.string  ->  FStar_Ident.ident = (fun str -> (mk_ident (str, dummyRange)))

# 285 "syntax.fs"

let text_of_id : ident  ->  Prims.string = (fun id -> id.FStar_Ident.idText)

# 286 "syntax.fs"

let text_of_path : Prims.string Prims.list  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))

# 287 "syntax.fs"

let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))

# 288 "syntax.fs"

let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))

# 289 "syntax.fs"

let path_of_lid : FStar_Ident.lident  ->  Prims.string Prims.list = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))

# 290 "syntax.fs"

let ids_of_lid : FStar_Ident.lident  ->  FStar_Ident.ident Prims.list = (fun lid -> (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))

# 291 "syntax.fs"

let lid_of_ids : ident Prims.list  ->  FStar_Ident.lident = (fun ids -> (let _25_320 = (FStar_Util.prefix ids)
in (match (_25_320) with
| (ns, id) -> begin
(let nsstr = (let _127_1272 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _127_1272 text_of_path))
in {FStar_Ident.ns = ns; FStar_Ident.ident = id; FStar_Ident.nsstr = nsstr; FStar_Ident.str = if (nsstr = "") then begin
id.FStar_Ident.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.FStar_Ident.idText)
end})
end)))

# 298 "syntax.fs"

let lid_of_path : Prims.string Prims.list  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun path pos -> (let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

# 301 "syntax.fs"

let text_of_lid : FStar_Ident.lident  ->  Prims.string = (fun lid -> lid.FStar_Ident.str)

# 302 "syntax.fs"

let lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun l1 l2 -> (l1.FStar_Ident.str = l2.FStar_Ident.str))

# 303 "syntax.fs"

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.FStar_Ident.idText = bvd2.realname.FStar_Ident.idText))

# 304 "syntax.fs"

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_25_335), FStar_Util.Inr (_25_338)) -> begin
(- (1))
end
| (FStar_Util.Inr (_25_342), FStar_Util.Inl (_25_345)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end))

# 310 "syntax.fs"

let lid_with_range : FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let id = (let _25_360 = lid.FStar_Ident.ident
in {FStar_Ident.idText = _25_360.FStar_Ident.idText; FStar_Ident.idRange = r})
in (let _25_363 = lid
in {FStar_Ident.ns = _25_363.FStar_Ident.ns; FStar_Ident.ident = id; FStar_Ident.nsstr = _25_363.FStar_Ident.nsstr; FStar_Ident.str = _25_363.FStar_Ident.str})))

# 313 "syntax.fs"

let range_of_lid : FStar_Ident.lid  ->  FStar_Range.range = (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idRange)

# 314 "syntax.fs"

let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

# 323 "syntax.fs"

let syn = (fun p k f -> (f k p))

# 324 "syntax.fs"

let mk_fvs = (fun _25_374 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 325 "syntax.fs"

let mk_uvs = (fun _25_375 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 326 "syntax.fs"

let new_ftv_set = (fun _25_376 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.FStar_Ident.idText y.v.realname.FStar_Ident.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.FStar_Ident.idText)))
end))

# 327 "syntax.fs"

let new_uv_set = (fun _25_380 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

# 328 "syntax.fs"

let new_uvt_set = (fun _25_383 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _25_391 _25_395 -> (match ((_25_391, _25_395)) with
| ((x, _25_390), (y, _25_394)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _25_387 -> (match (_25_387) with
| (x, _25_386) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 329 "syntax.fs"

let no_fvs : freevars = (let _127_1337 = (new_ftv_set ())
in (let _127_1336 = (new_ftv_set ())
in {ftvs = _127_1337; fxvs = _127_1336}))

# 333 "syntax.fs"

let no_uvs : uvars = (let _127_1340 = (new_uv_set ())
in (let _127_1339 = (new_uvt_set ())
in (let _127_1338 = (new_uvt_set ())
in {uvars_k = _127_1340; uvars_t = _127_1339; uvars_e = _127_1338})))

# 338 "syntax.fs"

let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 339 "syntax.fs"

let memo_no_fvs : freevars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_fvs)))

# 340 "syntax.fs"

let freevars_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  freevars = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _25_1 -> (match (_25_1) with
| FStar_Util.Inl (btv) -> begin
(let _25_401 = out
in (let _127_1345 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _127_1345; fxvs = _25_401.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(let _25_405 = out
in (let _127_1346 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _25_405.ftvs; fxvs = _127_1346}))
end)) no_fvs)))

# 344 "syntax.fs"

let list_of_freevars : freevars  ->  (btvar, bvvar) FStar_Util.either Prims.list = (fun fvs -> (let _127_1354 = (let _127_1350 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _127_1350 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _127_1353 = (let _127_1352 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _127_1352 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _127_1354 _127_1353))))

# 348 "syntax.fs"

let get_unit_ref : Prims.unit  ->  Prims.unit Prims.option FStar_ST.ref = (fun _25_410 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (())))
in (let _25_412 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 350 "syntax.fs"

let mk_Kind_type : (knd', Prims.unit) syntax = (let _127_1359 = (get_unit_ref ())
in (let _127_1358 = (mk_fvs ())
in (let _127_1357 = (mk_uvs ())
in {n = Kind_type; tk = _127_1359; pos = dummyRange; fvs = _127_1358; uvs = _127_1357})))

# 351 "syntax.fs"

let mk_Kind_effect : (knd', Prims.unit) syntax = (let _127_1362 = (get_unit_ref ())
in (let _127_1361 = (mk_fvs ())
in (let _127_1360 = (mk_uvs ())
in {n = Kind_effect; tk = _127_1362; pos = dummyRange; fvs = _127_1361; uvs = _127_1360})))

# 352 "syntax.fs"

let mk_Kind_abbrev : (kabbrev * knd)  ->  FStar_Range.range  ->  knd = (fun _25_416 p -> (match (_25_416) with
| (kabr, k) -> begin
(let _127_1369 = (get_unit_ref ())
in (let _127_1368 = (mk_fvs ())
in (let _127_1367 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _127_1369; pos = p; fvs = _127_1368; uvs = _127_1367})))
end))

# 358 "syntax.fs"

let mk_Kind_arrow : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _25_420 p -> (match (_25_420) with
| (bs, k) -> begin
(let _127_1376 = (get_unit_ref ())
in (let _127_1375 = (mk_fvs ())
in (let _127_1374 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _127_1376; pos = p; fvs = _127_1375; uvs = _127_1374})))
end))

# 364 "syntax.fs"

let mk_Kind_arrow' : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * knd)  ->  FStar_Range.range  ->  knd = (fun _25_424 p -> (match (_25_424) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _25_428 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _25_434 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

# 371 "syntax.fs"

let mk_Kind_uvar : uvar_k_app  ->  FStar_Range.range  ->  (knd', Prims.unit) syntax = (fun uv p -> (let _127_1387 = (get_unit_ref ())
in (let _127_1386 = (mk_fvs ())
in (let _127_1385 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _127_1387; pos = p; fvs = _127_1386; uvs = _127_1385}))))

# 378 "syntax.fs"

let mk_Kind_lam : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _25_439 p -> (match (_25_439) with
| (vs, k) -> begin
(let _127_1394 = (get_unit_ref ())
in (let _127_1393 = (mk_fvs ())
in (let _127_1392 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _127_1394; pos = p; fvs = _127_1393; uvs = _127_1392})))
end))

# 384 "syntax.fs"

let mk_Kind_delayed : (knd * subst_t * knd Prims.option FStar_ST.ref)  ->  FStar_Range.range  ->  knd = (fun _25_444 p -> (match (_25_444) with
| (k, s, m) -> begin
(let _127_1401 = (get_unit_ref ())
in (let _127_1400 = (mk_fvs ())
in (let _127_1399 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _127_1401; pos = p; fvs = _127_1400; uvs = _127_1399})))
end))

# 391 "syntax.fs"

let mk_Kind_unknown : (knd', Prims.unit) syntax = (let _127_1404 = (get_unit_ref ())
in (let _127_1403 = (mk_fvs ())
in (let _127_1402 = (mk_uvs ())
in {n = Kind_unknown; tk = _127_1404; pos = dummyRange; fvs = _127_1403; uvs = _127_1402})))

# 394 "syntax.fs"

let get_knd_nref : Prims.unit  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun _25_446 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _25_448 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 395 "syntax.fs"

let get_knd_ref : (knd', Prims.unit) syntax Prims.option  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun k -> (let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (let _25_452 = (FStar_ST.op_Colon_Equals x k)
in x)))

# 397 "syntax.fs"

let mk_Typ_btvar : btvar  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun x k p -> (let _127_1417 = (get_knd_ref k)
in (let _127_1416 = (mk_fvs ())
in (let _127_1415 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _127_1417; pos = p; fvs = _127_1416; uvs = _127_1415}))))

# 398 "syntax.fs"

let mk_Typ_const : ftvar  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun x k p -> (let _127_1424 = (get_knd_ref k)
in {n = Typ_const (x); tk = _127_1424; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

# 399 "syntax.fs"

let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _25_465 -> begin
Typ_fun ((bs, c))
end))

# 403 "syntax.fs"

let mk_Typ_fun : (binders * comp)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_468 k p -> (match (_25_468) with
| (bs, c) -> begin
(let _127_1437 = (check_fun bs c p)
in (let _127_1436 = (FStar_Util.mk_ref k)
in (let _127_1435 = (mk_fvs ())
in (let _127_1434 = (mk_uvs ())
in {n = _127_1437; tk = _127_1436; pos = p; fvs = _127_1435; uvs = _127_1434}))))
end))

# 409 "syntax.fs"

let mk_Typ_refine : (bvvar * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_473 k p -> (match (_25_473) with
| (x, phi) -> begin
(let _127_1446 = (FStar_Util.mk_ref k)
in (let _127_1445 = (mk_fvs ())
in (let _127_1444 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _127_1446; pos = p; fvs = _127_1445; uvs = _127_1444})))
end))

# 415 "syntax.fs"

let mk_Typ_app : (typ * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_478 k p -> (match (_25_478) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _25_483 -> begin
(let _127_1455 = (FStar_Util.mk_ref k)
in (let _127_1454 = (mk_fvs ())
in (let _127_1453 = (mk_uvs ())
in {n = Typ_app ((t1, args)); tk = _127_1455; pos = p; fvs = _127_1454; uvs = _127_1453})))
end)
end))

# 425 "syntax.fs"

let mk_Typ_app' : (typ * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_486 k p -> (match (_25_486) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _25_491 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

# 429 "syntax.fs"

let extend_typ_app : ((typ', (knd', Prims.unit) syntax) syntax * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option))  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_494 k p -> (match (_25_494) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _25_502 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

# 432 "syntax.fs"

let mk_Typ_lam : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_505 k p -> (match (_25_505) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _25_510 -> begin
(let _127_1476 = (FStar_Util.mk_ref k)
in (let _127_1475 = (mk_fvs ())
in (let _127_1474 = (mk_uvs ())
in {n = Typ_lam ((b, t)); tk = _127_1476; pos = p; fvs = _127_1475; uvs = _127_1474})))
end)
end))

# 442 "syntax.fs"

let mk_Typ_lam' : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _25_513 k p -> (match (_25_513) with
| (bs, t) -> begin
(mk_Typ_lam (bs, t) k p)
end))

# 445 "syntax.fs"

let mk_Typ_ascribed' : (typ * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_518 k' p -> (match (_25_518) with
| (t, k) -> begin
(let _127_1491 = (FStar_Util.mk_ref k')
in (let _127_1490 = (mk_fvs ())
in (let _127_1489 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _127_1491; pos = p; fvs = _127_1490; uvs = _127_1489})))
end))

# 452 "syntax.fs"

let mk_Typ_ascribed : (typ * knd)  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_523 p -> (match (_25_523) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

# 454 "syntax.fs"

let mk_Typ_meta' : meta_t  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun m k p -> (let _127_1504 = (FStar_Util.mk_ref k)
in (let _127_1503 = (mk_fvs ())
in (let _127_1502 = (mk_uvs ())
in {n = Typ_meta (m); tk = _127_1504; pos = p; fvs = _127_1503; uvs = _127_1502}))))

# 460 "syntax.fs"

let mk_Typ_meta : meta_t  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _127_1507 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _127_1507 t.pos))
end))

# 467 "syntax.fs"

let mk_Typ_uvar' : (uvar_t * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_560 k' p -> (match (_25_560) with
| (u, k) -> begin
(let _127_1516 = (get_knd_ref k')
in (let _127_1515 = (mk_fvs ())
in (let _127_1514 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _127_1516; pos = p; fvs = _127_1515; uvs = _127_1514})))
end))

# 474 "syntax.fs"

let mk_Typ_uvar : (uvar_t * knd)  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_565 p -> (match (_25_565) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

# 475 "syntax.fs"

let mk_Typ_delayed : ((typ', (knd', Prims.unit) syntax) syntax * subst_t * typ Prims.option FStar_ST.ref)  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun _25_570 k p -> (match (_25_570) with
| (t, s, m) -> begin
(let _127_1536 = (match (t.n) with
| Typ_delayed (_25_574) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _25_577 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _127_1535 = (FStar_Util.mk_ref k)
in (let _127_1534 = (mk_fvs ())
in (let _127_1533 = (mk_uvs ())
in {n = _127_1536; tk = _127_1535; pos = p; fvs = _127_1534; uvs = _127_1533}))))
end))

# 481 "syntax.fs"

let mk_Typ_delayed' : ((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either  ->  knd Prims.option  ->  FStar_Range.range  ->  (typ', (knd', Prims.unit) syntax) syntax = (fun st k p -> (let _127_1558 = (let _127_1554 = (let _127_1553 = (FStar_Util.mk_ref None)
in (st, _127_1553))
in Typ_delayed (_127_1554))
in (let _127_1557 = (FStar_Util.mk_ref k)
in (let _127_1556 = (mk_fvs ())
in (let _127_1555 = (mk_uvs ())
in {n = _127_1558; tk = _127_1557; pos = p; fvs = _127_1556; uvs = _127_1555})))))

# 488 "syntax.fs"

let mk_Typ_unknown : (typ', (knd', Prims.unit) syntax) syntax = (let _127_1561 = (get_knd_nref ())
in (let _127_1560 = (mk_fvs ())
in (let _127_1559 = (mk_uvs ())
in {n = Typ_unknown; tk = _127_1561; pos = dummyRange; fvs = _127_1560; uvs = _127_1559})))

# 489 "syntax.fs"

let get_typ_nref : Prims.unit  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun _25_581 -> (match (()) with
| () -> begin
(let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _25_583 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 490 "syntax.fs"

let get_typ_ref : (typ', (knd', Prims.unit) syntax) syntax Prims.option  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun t -> (let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (let _25_587 = (FStar_ST.op_Colon_Equals x t)
in x)))

# 492 "syntax.fs"

let mk_Total : typ  ->  (comp', Prims.unit) syntax = (fun t -> (let _127_1570 = (FStar_Util.mk_ref None)
in (let _127_1569 = (mk_fvs ())
in (let _127_1568 = (mk_uvs ())
in {n = Total (t); tk = _127_1570; pos = t.pos; fvs = _127_1569; uvs = _127_1568}))))

# 498 "syntax.fs"

let mk_Comp : comp_typ  ->  (comp', Prims.unit) syntax = (fun ct -> (let _127_1575 = (FStar_Util.mk_ref None)
in (let _127_1574 = (mk_fvs ())
in (let _127_1573 = (mk_uvs ())
in {n = Comp (ct); tk = _127_1575; pos = ct.result_typ.pos; fvs = _127_1574; uvs = _127_1573}))))

# 504 "syntax.fs"

let mk_Exp_bvar : bvvar  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun x t p -> (let _127_1584 = (get_typ_ref t)
in (let _127_1583 = (mk_fvs ())
in (let _127_1582 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _127_1584; pos = p; fvs = _127_1583; uvs = _127_1582}))))

# 510 "syntax.fs"

let mk_Exp_fvar : (fvvar * fv_qual Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_596 t p -> (match (_25_596) with
| (x, b) -> begin
(let _127_1593 = (get_typ_ref t)
in (let _127_1592 = (mk_fvs ())
in (let _127_1591 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _127_1593; pos = p; fvs = _127_1592; uvs = _127_1591})))
end))

# 516 "syntax.fs"

let mk_Exp_constant : sconst  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun s t p -> (let _127_1602 = (get_typ_ref t)
in (let _127_1601 = (mk_fvs ())
in (let _127_1600 = (mk_uvs ())
in {n = Exp_constant (s); tk = _127_1602; pos = p; fvs = _127_1601; uvs = _127_1600}))))

# 522 "syntax.fs"

let mk_Exp_abs : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_604 t' p -> (match (_25_604) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _25_609 -> begin
(let _127_1611 = (get_typ_ref t')
in (let _127_1610 = (mk_fvs ())
in (let _127_1609 = (mk_uvs ())
in {n = Exp_abs ((b, e)); tk = _127_1611; pos = p; fvs = _127_1610; uvs = _127_1609})))
end)
end))

# 531 "syntax.fs"

let mk_Exp_abs' : (((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_612 t' p -> (match (_25_612) with
| (b, e) -> begin
(let _127_1621 = (match ((b, e.n)) with
| (_25_616, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _25_626) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _25_629 -> begin
Exp_abs ((b, e))
end)
in (let _127_1620 = (get_typ_ref t')
in (let _127_1619 = (mk_fvs ())
in (let _127_1618 = (mk_uvs ())
in {n = _127_1621; tk = _127_1620; pos = p; fvs = _127_1619; uvs = _127_1618}))))
end))

# 540 "syntax.fs"

let mk_Exp_app : (exp * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_632 t p -> (match (_25_632) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _25_637 -> begin
(let _127_1630 = (get_typ_ref t)
in (let _127_1629 = (mk_fvs ())
in (let _127_1628 = (mk_uvs ())
in {n = Exp_app ((e1, args)); tk = _127_1630; pos = p; fvs = _127_1629; uvs = _127_1628})))
end)
end))

# 549 "syntax.fs"

let mk_Exp_app_flat : ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_640 t p -> (match (_25_640) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _25_648 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

# 553 "syntax.fs"

let mk_Exp_app' : (exp * (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _25_651 t p -> (match (_25_651) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _25_656 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

# 557 "syntax.fs"

let rec pat_vars : (pat', ((knd', Prims.unit) syntax, (typ', (knd', Prims.unit) syntax) syntax) FStar_Util.either Prims.option) withinfo_t  ->  ((typ', (knd', Prims.unit) syntax) syntax bvdef, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef) FStar_Util.either Prims.list = (fun p -> (match (p.v) with
| Pat_cons (_25_659, _25_661, ps) -> begin
(let vars = (FStar_List.collect (fun _25_668 -> (match (_25_668) with
| (x, _25_667) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _25_683 -> begin
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
in if (not ((let _127_1651 = (FStar_List.tl vars)
in (let _127_1650 = (let _127_1649 = (let _127_1648 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _127_1648))
in (FStar_Util.for_all _127_1649))
in (FStar_All.pipe_right _127_1651 _127_1650))))) then begin
(let vars = (let _127_1655 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _127_1654 = (FStar_List.map (fun _25_2 -> (match (_25_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.FStar_Ident.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idText
end)) v)
in (FStar_Util.concat_l ", " _127_1654)))))
in (FStar_Util.concat_l ";\n" _127_1655))
in (let _127_1658 = (let _127_1657 = (let _127_1656 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_127_1656, p.p))
in Error (_127_1657))
in (Prims.raise _127_1658)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

# 584 "syntax.fs"

let mk_Exp_match : (exp * (pat * exp Prims.option * exp) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_715 t p -> (match (_25_715) with
| (e, pats) -> begin
(let _127_1667 = (get_typ_ref t)
in (let _127_1666 = (mk_fvs ())
in (let _127_1665 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _127_1667; pos = p; fvs = _127_1666; uvs = _127_1665})))
end))

# 591 "syntax.fs"

let mk_Exp_ascribed : (exp * typ * lident Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_721 t' p -> (match (_25_721) with
| (e, t, l) -> begin
(let _127_1676 = (get_typ_ref t')
in (let _127_1675 = (mk_fvs ())
in (let _127_1674 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _127_1676; pos = p; fvs = _127_1675; uvs = _127_1674})))
end))

# 597 "syntax.fs"

let mk_Exp_let : (letbindings * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_726 t p -> (match (_25_726) with
| (lbs, e) -> begin
(let _127_1685 = (get_typ_ref t)
in (let _127_1684 = (mk_fvs ())
in (let _127_1683 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _127_1685; pos = p; fvs = _127_1684; uvs = _127_1683})))
end))

# 605 "syntax.fs"

let mk_Exp_uvar' : (uvar_e * typ)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_731 t' p -> (match (_25_731) with
| (u, t) -> begin
(let _127_1694 = (get_typ_ref t')
in (let _127_1693 = (mk_fvs ())
in (let _127_1692 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _127_1694; pos = p; fvs = _127_1693; uvs = _127_1692})))
end))

# 612 "syntax.fs"

let mk_Exp_uvar : (uvar_e * typ)  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_736 p -> (match (_25_736) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

# 614 "syntax.fs"

let mk_Exp_delayed : (exp * subst_t * exp Prims.option FStar_ST.ref)  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun _25_741 t p -> (match (_25_741) with
| (e, s, m) -> begin
(let _127_1707 = (get_typ_ref t)
in (let _127_1706 = (mk_fvs ())
in (let _127_1705 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _127_1707; pos = p; fvs = _127_1706; uvs = _127_1705})))
end))

# 621 "syntax.fs"

let mk_Exp_meta' : meta_e  ->  typ Prims.option  ->  FStar_Range.range  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun m t p -> (let _127_1716 = (get_typ_ref t)
in (let _127_1715 = (mk_fvs ())
in (let _127_1714 = (mk_uvs ())
in {n = Exp_meta (m); tk = _127_1716; pos = p; fvs = _127_1715; uvs = _127_1714}))))

# 628 "syntax.fs"

let mk_Exp_meta : meta_e  ->  (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax = (fun m -> (match (m) with
| Meta_desugared (e, _25_750) -> begin
(let _127_1719 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _127_1719 e.pos))
end))

# 631 "syntax.fs"

let mk_lb : (lbname * lident * typ * exp)  ->  letbinding = (fun _25_757 -> (match (_25_757) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 633 "syntax.fs"

let mk_subst : subst  ->  subst = (fun s -> s)

# 634 "syntax.fs"

let extend_subst : (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list = (fun x s -> (x)::s)

# 635 "syntax.fs"

let argpos : arg  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _25_765) -> begin
t.pos
end
| (FStar_Util.Inr (e), _25_770) -> begin
e.pos
end))

# 639 "syntax.fs"

let tun : (typ', (knd', Prims.unit) syntax) syntax = mk_Typ_unknown

# 640 "syntax.fs"

let kun : (knd', Prims.unit) syntax = mk_Kind_unknown

# 641 "syntax.fs"

let ktype : (knd', Prims.unit) syntax = mk_Kind_type

# 642 "syntax.fs"

let keffect : (knd', Prims.unit) syntax = mk_Kind_effect

# 643 "syntax.fs"

let null_id : FStar_Ident.ident = (mk_ident ("_", dummyRange))

# 644 "syntax.fs"

let null_bvd = {ppname = null_id; realname = null_id}

# 645 "syntax.fs"

let null_bvar = (fun k -> {v = null_bvd; sort = k; p = dummyRange})

# 646 "syntax.fs"

let t_binder : btvar  ->  ((btvar, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) = (fun a -> (FStar_Util.Inl (a), None))

# 647 "syntax.fs"

let v_binder : bvvar  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, bvvar) FStar_Util.either * arg_qualifier Prims.option) = (fun a -> (FStar_Util.Inr (a), None))

# 648 "syntax.fs"

let null_t_binder : (knd', Prims.unit) syntax  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inl ((null_bvar t)), None))

# 649 "syntax.fs"

let null_v_binder : (typ', (knd', Prims.unit) syntax) syntax  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inr ((null_bvar t)), None))

# 650 "syntax.fs"

let itarg : (typ', (knd', Prims.unit) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inl (t), Some (Implicit (false))))

# 651 "syntax.fs"

let ivarg : (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun v -> (FStar_Util.Inr (v), Some (Implicit (false))))

# 652 "syntax.fs"

let targ : (typ', (knd', Prims.unit) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun t -> (FStar_Util.Inl (t), None))

# 653 "syntax.fs"

let varg : (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax  ->  (((typ', (knd', Prims.unit) syntax) syntax, (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax) FStar_Util.either * arg_qualifier Prims.option) = (fun v -> (FStar_Util.Inr (v), None))

# 654 "syntax.fs"

let is_null_pp = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 655 "syntax.fs"

let is_null_bvd = (fun b -> (b.realname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 656 "syntax.fs"

let is_null_bvar = (fun b -> (is_null_bvd b.v))

# 657 "syntax.fs"

let is_null_binder : binder  ->  Prims.bool = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _25_792) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _25_797) -> begin
(is_null_bvar x)
end))

# 661 "syntax.fs"

let freevars_of_binders : binders  ->  freevars = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _25_3 -> (match (_25_3) with
| (FStar_Util.Inl (btv), _25_805) -> begin
(let _25_807 = out
in (let _127_1756 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _127_1756; fxvs = _25_807.fxvs}))
end
| (FStar_Util.Inr (bxv), _25_812) -> begin
(let _25_814 = out
in (let _127_1757 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _25_814.ftvs; fxvs = _127_1757}))
end)) no_fvs)))

# 666 "syntax.fs"

let binders_of_list : (((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either Prims.list  ->  ((((typ', (knd', Prims.unit) syntax) syntax bvdef, (knd', Prims.unit) syntax) withinfo_t, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 667 "syntax.fs"

let binders_of_freevars : freevars  ->  ((btvar, ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef, (typ', (knd', Prims.unit) syntax) syntax) withinfo_t) FStar_Util.either * arg_qualifier Prims.option) Prims.list = (fun fvs -> (let _127_1766 = (let _127_1763 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _127_1763 (FStar_List.map t_binder)))
in (let _127_1765 = (let _127_1764 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _127_1764 (FStar_List.map v_binder)))
in (FStar_List.append _127_1766 _127_1765))))

# 669 "syntax.fs"

let is_implicit : arg_qualifier Prims.option  ->  Prims.bool = (fun _25_4 -> (match (_25_4) with
| Some (Implicit (_25_821)) -> begin
true
end
| _25_825 -> begin
false
end))

# 670 "syntax.fs"

let as_implicit : Prims.bool  ->  arg_qualifier Prims.option = (fun _25_5 -> (match (_25_5) with
| true -> begin
Some (Implicit (false))
end
| _25_829 -> begin
None
end))




