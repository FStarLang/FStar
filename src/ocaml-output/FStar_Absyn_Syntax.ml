
open Prims
# 24 "FStar.Absyn.Syntax.fst"
type ident =
FStar_Ident.ident

# 26 "FStar.Absyn.Syntax.fst"
type lident =
FStar_Ident.lid

# 27 "FStar.Absyn.Syntax.fst"
type l__LongIdent =
lident

# 29 "FStar.Absyn.Syntax.fst"
exception Err of (Prims.string)

# 29 "FStar.Absyn.Syntax.fst"
let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Absyn.Syntax.fst"
let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_18_7) -> begin
_18_7
end))

# 30 "FStar.Absyn.Syntax.fst"
exception Error of ((Prims.string * FStar_Range.range))

# 30 "FStar.Absyn.Syntax.fst"
let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Absyn.Syntax.fst"
let ___Error____0 = (fun projectee -> (match (projectee) with
| Error (_18_9) -> begin
_18_9
end))

# 31 "FStar.Absyn.Syntax.fst"
exception Warning of ((Prims.string * FStar_Range.range))

# 31 "FStar.Absyn.Syntax.fst"
let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.Absyn.Syntax.fst"
let ___Warning____0 = (fun projectee -> (match (projectee) with
| Warning (_18_11) -> begin
_18_11
end))

# 31 "FStar.Absyn.Syntax.fst"
type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}

# 33 "FStar.Absyn.Syntax.fst"
let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

# 37 "FStar.Absyn.Syntax.fst"
type 't var =
(lident, 't) withinfo_t

# 38 "FStar.Absyn.Syntax.fst"
type fieldname =
lident

# 39 "FStar.Absyn.Syntax.fst"
type 'a bvdef =
{ppname : ident; realname : ident}

# 40 "FStar.Absyn.Syntax.fst"
let is_Mkbvdef = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbvdef"))))

# 40 "FStar.Absyn.Syntax.fst"
type ('a, 't) bvar =
('a bvdef, 't) withinfo_t

# 41 "FStar.Absyn.Syntax.fst"
type sconst =
FStar_Const.sconst

# 47 "FStar.Absyn.Syntax.fst"
type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string Prims.option

# 49 "FStar.Absyn.Syntax.fst"
let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Absyn.Syntax.fst"
let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.Absyn.Syntax.fst"
let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_18_27) -> begin
_18_27
end))

# 50 "FStar.Absyn.Syntax.fst"
let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_18_30) -> begin
_18_30
end))

# 50 "FStar.Absyn.Syntax.fst"
type 'a memo =
'a Prims.option FStar_ST.ref

# 51 "FStar.Absyn.Syntax.fst"
type arg_qualifier =
| Implicit of Prims.bool
| Equality

# 53 "FStar.Absyn.Syntax.fst"
let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.Absyn.Syntax.fst"
let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.Absyn.Syntax.fst"
let ___Implicit____0 = (fun projectee -> (match (projectee) with
| Implicit (_18_34) -> begin
_18_34
end))

# 54 "FStar.Absyn.Syntax.fst"
type aqual =
arg_qualifier Prims.option

# 55 "FStar.Absyn.Syntax.fst"
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

# 57 "FStar.Absyn.Syntax.fst"
let is_Typ_btvar = (fun _discr_ -> (match (_discr_) with
| Typ_btvar (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.Absyn.Syntax.fst"
let is_Typ_const = (fun _discr_ -> (match (_discr_) with
| Typ_const (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.Absyn.Syntax.fst"
let is_Typ_fun = (fun _discr_ -> (match (_discr_) with
| Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.Absyn.Syntax.fst"
let is_Typ_refine = (fun _discr_ -> (match (_discr_) with
| Typ_refine (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.Absyn.Syntax.fst"
let is_Typ_app = (fun _discr_ -> (match (_discr_) with
| Typ_app (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.Absyn.Syntax.fst"
let is_Typ_lam = (fun _discr_ -> (match (_discr_) with
| Typ_lam (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.Absyn.Syntax.fst"
let is_Typ_ascribed = (fun _discr_ -> (match (_discr_) with
| Typ_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Absyn.Syntax.fst"
let is_Typ_meta = (fun _discr_ -> (match (_discr_) with
| Typ_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.Absyn.Syntax.fst"
let is_Typ_uvar = (fun _discr_ -> (match (_discr_) with
| Typ_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.Absyn.Syntax.fst"
let is_Typ_delayed = (fun _discr_ -> (match (_discr_) with
| Typ_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.Absyn.Syntax.fst"
let is_Typ_unknown = (fun _discr_ -> (match (_discr_) with
| Typ_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Absyn.Syntax.fst"
let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

# 80 "FStar.Absyn.Syntax.fst"
let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.Absyn.Syntax.fst"
let is_Comp = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.Absyn.Syntax.fst"
let is_TOTAL = (fun _discr_ -> (match (_discr_) with
| TOTAL (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.Absyn.Syntax.fst"
let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Absyn.Syntax.fst"
let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Absyn.Syntax.fst"
let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.Absyn.Syntax.fst"
let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Absyn.Syntax.fst"
let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Absyn.Syntax.fst"
let is_DECREASES = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "FStar.Absyn.Syntax.fst"
let is_Meta_pattern = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "FStar.Absyn.Syntax.fst"
let is_Meta_named = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "FStar.Absyn.Syntax.fst"
let is_Meta_labeled = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 96 "FStar.Absyn.Syntax.fst"
let is_Meta_refresh_label = (fun _discr_ -> (match (_discr_) with
| Meta_refresh_label (_) -> begin
true
end
| _ -> begin
false
end))

# 97 "FStar.Absyn.Syntax.fst"
let is_Meta_slack_formula = (fun _discr_ -> (match (_discr_) with
| Meta_slack_formula (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.Absyn.Syntax.fst"
let is_Uvar = (fun _ _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 100 "FStar.Absyn.Syntax.fst"
let is_Fixed = (fun _ _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "FStar.Absyn.Syntax.fst"
let is_Exp_bvar = (fun _discr_ -> (match (_discr_) with
| Exp_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.Absyn.Syntax.fst"
let is_Exp_fvar = (fun _discr_ -> (match (_discr_) with
| Exp_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.Absyn.Syntax.fst"
let is_Exp_constant = (fun _discr_ -> (match (_discr_) with
| Exp_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.Absyn.Syntax.fst"
let is_Exp_abs = (fun _discr_ -> (match (_discr_) with
| Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.Absyn.Syntax.fst"
let is_Exp_app = (fun _discr_ -> (match (_discr_) with
| Exp_app (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "FStar.Absyn.Syntax.fst"
let is_Exp_match = (fun _discr_ -> (match (_discr_) with
| Exp_match (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.Absyn.Syntax.fst"
let is_Exp_ascribed = (fun _discr_ -> (match (_discr_) with
| Exp_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.Absyn.Syntax.fst"
let is_Exp_let = (fun _discr_ -> (match (_discr_) with
| Exp_let (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.Absyn.Syntax.fst"
let is_Exp_uvar = (fun _discr_ -> (match (_discr_) with
| Exp_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Absyn.Syntax.fst"
let is_Exp_delayed = (fun _discr_ -> (match (_discr_) with
| Exp_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "FStar.Absyn.Syntax.fst"
let is_Exp_meta = (fun _discr_ -> (match (_discr_) with
| Exp_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 115 "FStar.Absyn.Syntax.fst"
let is_Meta_desugared = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

# 117 "FStar.Absyn.Syntax.fst"
let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "FStar.Absyn.Syntax.fst"
let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "FStar.Absyn.Syntax.fst"
let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop (_) -> begin
true
end
| _ -> begin
false
end))

# 120 "FStar.Absyn.Syntax.fst"
let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "FStar.Absyn.Syntax.fst"
let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "FStar.Absyn.Syntax.fst"
let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 124 "FStar.Absyn.Syntax.fst"
let is_Record_projector = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

# 125 "FStar.Absyn.Syntax.fst"
let is_Record_ctor = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 130 "FStar.Absyn.Syntax.fst"
let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

# 131 "FStar.Absyn.Syntax.fst"
let is_Pat_constant = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "FStar.Absyn.Syntax.fst"
let is_Pat_cons = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.Absyn.Syntax.fst"
let is_Pat_var = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "FStar.Absyn.Syntax.fst"
let is_Pat_tvar = (fun _discr_ -> (match (_discr_) with
| Pat_tvar (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "FStar.Absyn.Syntax.fst"
let is_Pat_wild = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.Absyn.Syntax.fst"
let is_Pat_twild = (fun _discr_ -> (match (_discr_) with
| Pat_twild (_) -> begin
true
end
| _ -> begin
false
end))

# 137 "FStar.Absyn.Syntax.fst"
let is_Pat_dot_term = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

# 138 "FStar.Absyn.Syntax.fst"
let is_Pat_dot_typ = (fun _discr_ -> (match (_discr_) with
| Pat_dot_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "FStar.Absyn.Syntax.fst"
let is_Kind_type = (fun _discr_ -> (match (_discr_) with
| Kind_type (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "FStar.Absyn.Syntax.fst"
let is_Kind_effect = (fun _discr_ -> (match (_discr_) with
| Kind_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "FStar.Absyn.Syntax.fst"
let is_Kind_abbrev = (fun _discr_ -> (match (_discr_) with
| Kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 144 "FStar.Absyn.Syntax.fst"
let is_Kind_arrow = (fun _discr_ -> (match (_discr_) with
| Kind_arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "FStar.Absyn.Syntax.fst"
let is_Kind_uvar = (fun _discr_ -> (match (_discr_) with
| Kind_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "FStar.Absyn.Syntax.fst"
let is_Kind_lam = (fun _discr_ -> (match (_discr_) with
| Kind_lam (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "FStar.Absyn.Syntax.fst"
let is_Kind_delayed = (fun _discr_ -> (match (_discr_) with
| Kind_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 148 "FStar.Absyn.Syntax.fst"
let is_Kind_unknown = (fun _discr_ -> (match (_discr_) with
| Kind_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 154 "FStar.Absyn.Syntax.fst"
let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

# 165 "FStar.Absyn.Syntax.fst"
let is_Mkfreevars : freevars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfreevars"))))

# 169 "FStar.Absyn.Syntax.fst"
let is_Mkuvars : uvars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkuvars"))))

# 174 "FStar.Absyn.Syntax.fst"
let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

# 57 "FStar.Absyn.Syntax.fst"
let ___Typ_btvar____0 = (fun projectee -> (match (projectee) with
| Typ_btvar (_18_58) -> begin
_18_58
end))

# 58 "FStar.Absyn.Syntax.fst"
let ___Typ_const____0 = (fun projectee -> (match (projectee) with
| Typ_const (_18_61) -> begin
_18_61
end))

# 59 "FStar.Absyn.Syntax.fst"
let ___Typ_fun____0 = (fun projectee -> (match (projectee) with
| Typ_fun (_18_64) -> begin
_18_64
end))

# 60 "FStar.Absyn.Syntax.fst"
let ___Typ_refine____0 = (fun projectee -> (match (projectee) with
| Typ_refine (_18_67) -> begin
_18_67
end))

# 61 "FStar.Absyn.Syntax.fst"
let ___Typ_app____0 = (fun projectee -> (match (projectee) with
| Typ_app (_18_70) -> begin
_18_70
end))

# 62 "FStar.Absyn.Syntax.fst"
let ___Typ_lam____0 = (fun projectee -> (match (projectee) with
| Typ_lam (_18_73) -> begin
_18_73
end))

# 63 "FStar.Absyn.Syntax.fst"
let ___Typ_ascribed____0 = (fun projectee -> (match (projectee) with
| Typ_ascribed (_18_76) -> begin
_18_76
end))

# 64 "FStar.Absyn.Syntax.fst"
let ___Typ_meta____0 = (fun projectee -> (match (projectee) with
| Typ_meta (_18_79) -> begin
_18_79
end))

# 65 "FStar.Absyn.Syntax.fst"
let ___Typ_uvar____0 = (fun projectee -> (match (projectee) with
| Typ_uvar (_18_82) -> begin
_18_82
end))

# 66 "FStar.Absyn.Syntax.fst"
let ___Typ_delayed____0 = (fun projectee -> (match (projectee) with
| Typ_delayed (_18_85) -> begin
_18_85
end))

# 80 "FStar.Absyn.Syntax.fst"
let ___Total____0 = (fun projectee -> (match (projectee) with
| Total (_18_89) -> begin
_18_89
end))

# 81 "FStar.Absyn.Syntax.fst"
let ___Comp____0 = (fun projectee -> (match (projectee) with
| Comp (_18_92) -> begin
_18_92
end))

# 90 "FStar.Absyn.Syntax.fst"
let ___DECREASES____0 = (fun projectee -> (match (projectee) with
| DECREASES (_18_95) -> begin
_18_95
end))

# 93 "FStar.Absyn.Syntax.fst"
let ___Meta_pattern____0 = (fun projectee -> (match (projectee) with
| Meta_pattern (_18_98) -> begin
_18_98
end))

# 94 "FStar.Absyn.Syntax.fst"
let ___Meta_named____0 = (fun projectee -> (match (projectee) with
| Meta_named (_18_101) -> begin
_18_101
end))

# 95 "FStar.Absyn.Syntax.fst"
let ___Meta_labeled____0 = (fun projectee -> (match (projectee) with
| Meta_labeled (_18_104) -> begin
_18_104
end))

# 96 "FStar.Absyn.Syntax.fst"
let ___Meta_refresh_label____0 = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_18_107) -> begin
_18_107
end))

# 97 "FStar.Absyn.Syntax.fst"
let ___Meta_slack_formula____0 = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_18_110) -> begin
_18_110
end))

# 100 "FStar.Absyn.Syntax.fst"
let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_18_113) -> begin
_18_113
end))

# 102 "FStar.Absyn.Syntax.fst"
let ___Exp_bvar____0 = (fun projectee -> (match (projectee) with
| Exp_bvar (_18_116) -> begin
_18_116
end))

# 103 "FStar.Absyn.Syntax.fst"
let ___Exp_fvar____0 = (fun projectee -> (match (projectee) with
| Exp_fvar (_18_119) -> begin
_18_119
end))

# 104 "FStar.Absyn.Syntax.fst"
let ___Exp_constant____0 = (fun projectee -> (match (projectee) with
| Exp_constant (_18_122) -> begin
_18_122
end))

# 105 "FStar.Absyn.Syntax.fst"
let ___Exp_abs____0 = (fun projectee -> (match (projectee) with
| Exp_abs (_18_125) -> begin
_18_125
end))

# 106 "FStar.Absyn.Syntax.fst"
let ___Exp_app____0 = (fun projectee -> (match (projectee) with
| Exp_app (_18_128) -> begin
_18_128
end))

# 107 "FStar.Absyn.Syntax.fst"
let ___Exp_match____0 = (fun projectee -> (match (projectee) with
| Exp_match (_18_131) -> begin
_18_131
end))

# 108 "FStar.Absyn.Syntax.fst"
let ___Exp_ascribed____0 = (fun projectee -> (match (projectee) with
| Exp_ascribed (_18_134) -> begin
_18_134
end))

# 109 "FStar.Absyn.Syntax.fst"
let ___Exp_let____0 = (fun projectee -> (match (projectee) with
| Exp_let (_18_137) -> begin
_18_137
end))

# 110 "FStar.Absyn.Syntax.fst"
let ___Exp_uvar____0 = (fun projectee -> (match (projectee) with
| Exp_uvar (_18_140) -> begin
_18_140
end))

# 111 "FStar.Absyn.Syntax.fst"
let ___Exp_delayed____0 = (fun projectee -> (match (projectee) with
| Exp_delayed (_18_143) -> begin
_18_143
end))

# 112 "FStar.Absyn.Syntax.fst"
let ___Exp_meta____0 = (fun projectee -> (match (projectee) with
| Exp_meta (_18_146) -> begin
_18_146
end))

# 115 "FStar.Absyn.Syntax.fst"
let ___Meta_desugared____0 = (fun projectee -> (match (projectee) with
| Meta_desugared (_18_148) -> begin
_18_148
end))

# 124 "FStar.Absyn.Syntax.fst"
let ___Record_projector____0 = (fun projectee -> (match (projectee) with
| Record_projector (_18_151) -> begin
_18_151
end))

# 125 "FStar.Absyn.Syntax.fst"
let ___Record_ctor____0 = (fun projectee -> (match (projectee) with
| Record_ctor (_18_154) -> begin
_18_154
end))

# 130 "FStar.Absyn.Syntax.fst"
let ___Pat_disj____0 = (fun projectee -> (match (projectee) with
| Pat_disj (_18_157) -> begin
_18_157
end))

# 131 "FStar.Absyn.Syntax.fst"
let ___Pat_constant____0 = (fun projectee -> (match (projectee) with
| Pat_constant (_18_160) -> begin
_18_160
end))

# 132 "FStar.Absyn.Syntax.fst"
let ___Pat_cons____0 = (fun projectee -> (match (projectee) with
| Pat_cons (_18_163) -> begin
_18_163
end))

# 133 "FStar.Absyn.Syntax.fst"
let ___Pat_var____0 = (fun projectee -> (match (projectee) with
| Pat_var (_18_166) -> begin
_18_166
end))

# 134 "FStar.Absyn.Syntax.fst"
let ___Pat_tvar____0 = (fun projectee -> (match (projectee) with
| Pat_tvar (_18_169) -> begin
_18_169
end))

# 135 "FStar.Absyn.Syntax.fst"
let ___Pat_wild____0 = (fun projectee -> (match (projectee) with
| Pat_wild (_18_172) -> begin
_18_172
end))

# 136 "FStar.Absyn.Syntax.fst"
let ___Pat_twild____0 = (fun projectee -> (match (projectee) with
| Pat_twild (_18_175) -> begin
_18_175
end))

# 137 "FStar.Absyn.Syntax.fst"
let ___Pat_dot_term____0 = (fun projectee -> (match (projectee) with
| Pat_dot_term (_18_178) -> begin
_18_178
end))

# 138 "FStar.Absyn.Syntax.fst"
let ___Pat_dot_typ____0 = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_18_181) -> begin
_18_181
end))

# 143 "FStar.Absyn.Syntax.fst"
let ___Kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Kind_abbrev (_18_184) -> begin
_18_184
end))

# 144 "FStar.Absyn.Syntax.fst"
let ___Kind_arrow____0 = (fun projectee -> (match (projectee) with
| Kind_arrow (_18_187) -> begin
_18_187
end))

# 145 "FStar.Absyn.Syntax.fst"
let ___Kind_uvar____0 = (fun projectee -> (match (projectee) with
| Kind_uvar (_18_190) -> begin
_18_190
end))

# 146 "FStar.Absyn.Syntax.fst"
let ___Kind_lam____0 = (fun projectee -> (match (projectee) with
| Kind_lam (_18_193) -> begin
_18_193
end))

# 147 "FStar.Absyn.Syntax.fst"
let ___Kind_delayed____0 = (fun projectee -> (match (projectee) with
| Kind_delayed (_18_196) -> begin
_18_196
end))

# 184 "FStar.Absyn.Syntax.fst"
type subst =
subst_elt Prims.list

# 186 "FStar.Absyn.Syntax.fst"
type either_var =
(btvar, bvvar) FStar_Util.either

# 187 "FStar.Absyn.Syntax.fst"
type freevars_l =
either_var Prims.list

# 188 "FStar.Absyn.Syntax.fst"
type formula =
typ

# 189 "FStar.Absyn.Syntax.fst"
type formulae =
typ Prims.list

# 190 "FStar.Absyn.Syntax.fst"
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

# 192 "FStar.Absyn.Syntax.fst"
let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 193 "FStar.Absyn.Syntax.fst"
let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 194 "FStar.Absyn.Syntax.fst"
let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque (_) -> begin
true
end
| _ -> begin
false
end))

# 195 "FStar.Absyn.Syntax.fst"
let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 196 "FStar.Absyn.Syntax.fst"
let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 197 "FStar.Absyn.Syntax.fst"
let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 198 "FStar.Absyn.Syntax.fst"
let is_Discriminator = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

# 199 "FStar.Absyn.Syntax.fst"
let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

# 200 "FStar.Absyn.Syntax.fst"
let is_RecordType = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

# 201 "FStar.Absyn.Syntax.fst"
let is_RecordConstructor = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 202 "FStar.Absyn.Syntax.fst"
let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 203 "FStar.Absyn.Syntax.fst"
let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 204 "FStar.Absyn.Syntax.fst"
let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 205 "FStar.Absyn.Syntax.fst"
let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 206 "FStar.Absyn.Syntax.fst"
let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 198 "FStar.Absyn.Syntax.fst"
let ___Discriminator____0 = (fun projectee -> (match (projectee) with
| Discriminator (_18_203) -> begin
_18_203
end))

# 199 "FStar.Absyn.Syntax.fst"
let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_18_206) -> begin
_18_206
end))

# 200 "FStar.Absyn.Syntax.fst"
let ___RecordType____0 = (fun projectee -> (match (projectee) with
| RecordType (_18_209) -> begin
_18_209
end))

# 201 "FStar.Absyn.Syntax.fst"
let ___RecordConstructor____0 = (fun projectee -> (match (projectee) with
| RecordConstructor (_18_212) -> begin
_18_212
end))

# 203 "FStar.Absyn.Syntax.fst"
let ___DefaultEffect____0 = (fun projectee -> (match (projectee) with
| DefaultEffect (_18_215) -> begin
_18_215
end))

# 206 "FStar.Absyn.Syntax.fst"
type tycon =
(lident * binders * knd)

# 208 "FStar.Absyn.Syntax.fst"
type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

# 209 "FStar.Absyn.Syntax.fst"
let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

# 213 "FStar.Absyn.Syntax.fst"
type sub_eff =
{source : lident; target : lident; lift : typ}

# 214 "FStar.Absyn.Syntax.fst"
let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

# 218 "FStar.Absyn.Syntax.fst"
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

# 219 "FStar.Absyn.Syntax.fst"
let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

# 240 "FStar.Absyn.Syntax.fst"
let is_Sig_tycon = (fun _discr_ -> (match (_discr_) with
| Sig_tycon (_) -> begin
true
end
| _ -> begin
false
end))

# 241 "FStar.Absyn.Syntax.fst"
let is_Sig_kind_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 242 "FStar.Absyn.Syntax.fst"
let is_Sig_typ_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_typ_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 243 "FStar.Absyn.Syntax.fst"
let is_Sig_datacon = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

# 244 "FStar.Absyn.Syntax.fst"
let is_Sig_val_decl = (fun _discr_ -> (match (_discr_) with
| Sig_val_decl (_) -> begin
true
end
| _ -> begin
false
end))

# 245 "FStar.Absyn.Syntax.fst"
let is_Sig_assume = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

# 246 "FStar.Absyn.Syntax.fst"
let is_Sig_let = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

# 247 "FStar.Absyn.Syntax.fst"
let is_Sig_main = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

# 248 "FStar.Absyn.Syntax.fst"
let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

# 249 "FStar.Absyn.Syntax.fst"
let is_Sig_new_effect = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 250 "FStar.Absyn.Syntax.fst"
let is_Sig_sub_effect = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 251 "FStar.Absyn.Syntax.fst"
let is_Sig_effect_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 252 "FStar.Absyn.Syntax.fst"
let is_Sig_pragma = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 240 "FStar.Absyn.Syntax.fst"
let ___Sig_tycon____0 = (fun projectee -> (match (projectee) with
| Sig_tycon (_18_245) -> begin
_18_245
end))

# 241 "FStar.Absyn.Syntax.fst"
let ___Sig_kind_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_18_248) -> begin
_18_248
end))

# 242 "FStar.Absyn.Syntax.fst"
let ___Sig_typ_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_18_251) -> begin
_18_251
end))

# 243 "FStar.Absyn.Syntax.fst"
let ___Sig_datacon____0 = (fun projectee -> (match (projectee) with
| Sig_datacon (_18_254) -> begin
_18_254
end))

# 244 "FStar.Absyn.Syntax.fst"
let ___Sig_val_decl____0 = (fun projectee -> (match (projectee) with
| Sig_val_decl (_18_257) -> begin
_18_257
end))

# 245 "FStar.Absyn.Syntax.fst"
let ___Sig_assume____0 = (fun projectee -> (match (projectee) with
| Sig_assume (_18_260) -> begin
_18_260
end))

# 246 "FStar.Absyn.Syntax.fst"
let ___Sig_let____0 = (fun projectee -> (match (projectee) with
| Sig_let (_18_263) -> begin
_18_263
end))

# 247 "FStar.Absyn.Syntax.fst"
let ___Sig_main____0 = (fun projectee -> (match (projectee) with
| Sig_main (_18_266) -> begin
_18_266
end))

# 248 "FStar.Absyn.Syntax.fst"
let ___Sig_bundle____0 = (fun projectee -> (match (projectee) with
| Sig_bundle (_18_269) -> begin
_18_269
end))

# 249 "FStar.Absyn.Syntax.fst"
let ___Sig_new_effect____0 = (fun projectee -> (match (projectee) with
| Sig_new_effect (_18_272) -> begin
_18_272
end))

# 250 "FStar.Absyn.Syntax.fst"
let ___Sig_sub_effect____0 = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_18_275) -> begin
_18_275
end))

# 251 "FStar.Absyn.Syntax.fst"
let ___Sig_effect_abbrev____0 = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_18_278) -> begin
_18_278
end))

# 252 "FStar.Absyn.Syntax.fst"
let ___Sig_pragma____0 = (fun projectee -> (match (projectee) with
| Sig_pragma (_18_281) -> begin
_18_281
end))

# 252 "FStar.Absyn.Syntax.fst"
type sigelts =
sigelt Prims.list

# 253 "FStar.Absyn.Syntax.fst"
type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}

# 255 "FStar.Absyn.Syntax.fst"
let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

# 261 "FStar.Absyn.Syntax.fst"
type ktec =
| K of knd
| T of (typ * knd Prims.option)
| E of exp
| C of comp

# 264 "FStar.Absyn.Syntax.fst"
let is_K = (fun _discr_ -> (match (_discr_) with
| K (_) -> begin
true
end
| _ -> begin
false
end))

# 265 "FStar.Absyn.Syntax.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 266 "FStar.Absyn.Syntax.fst"
let is_E = (fun _discr_ -> (match (_discr_) with
| E (_) -> begin
true
end
| _ -> begin
false
end))

# 267 "FStar.Absyn.Syntax.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 264 "FStar.Absyn.Syntax.fst"
let ___K____0 = (fun projectee -> (match (projectee) with
| K (_18_290) -> begin
_18_290
end))

# 265 "FStar.Absyn.Syntax.fst"
let ___T____0 = (fun projectee -> (match (projectee) with
| T (_18_293) -> begin
_18_293
end))

# 266 "FStar.Absyn.Syntax.fst"
let ___E____0 = (fun projectee -> (match (projectee) with
| E (_18_296) -> begin
_18_296
end))

# 267 "FStar.Absyn.Syntax.fst"
let ___C____0 = (fun projectee -> (match (projectee) with
| C (_18_299) -> begin
_18_299
end))

# 267 "FStar.Absyn.Syntax.fst"
type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

# 269 "FStar.Absyn.Syntax.fst"
let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

# 274 "FStar.Absyn.Syntax.fst"
type path =
Prims.string Prims.list

# 372 "FStar.Absyn.Syntax.fst"
let dummyRange : FStar_Range.range = 0L

# 376 "FStar.Absyn.Syntax.fst"
let withinfo = (fun v s r -> {v = v; sort = s; p = r})

# 377 "FStar.Absyn.Syntax.fst"
let withsort = (fun v s -> (withinfo v s dummyRange))

# 378 "FStar.Absyn.Syntax.fst"
let mk_ident : (Prims.string * FStar_Range.range)  ->  ident = (fun _18_335 -> (match (_18_335) with
| (text, range) -> begin
{FStar_Ident.idText = text; FStar_Ident.idRange = range}
end))

# 379 "FStar.Absyn.Syntax.fst"
let id_of_text : Prims.string  ->  ident = (fun str -> (mk_ident (str, dummyRange)))

# 380 "FStar.Absyn.Syntax.fst"
let text_of_id : ident  ->  Prims.string = (fun id -> id.FStar_Ident.idText)

# 381 "FStar.Absyn.Syntax.fst"
let text_of_path : path  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))

# 382 "FStar.Absyn.Syntax.fst"
let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))

# 383 "FStar.Absyn.Syntax.fst"
let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))

# 384 "FStar.Absyn.Syntax.fst"
let path_of_lid : lident  ->  path = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))

# 385 "FStar.Absyn.Syntax.fst"
let ids_of_lid : lident  ->  ident Prims.list = (fun lid -> (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))

# 386 "FStar.Absyn.Syntax.fst"
let lid_of_ids : ident Prims.list  ->  lident = (fun ids -> (
# 388 "FStar.Absyn.Syntax.fst"
let _18_346 = (FStar_Util.prefix ids)
in (match (_18_346) with
| (ns, id) -> begin
(
# 389 "FStar.Absyn.Syntax.fst"
let nsstr = (let _97_1285 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _97_1285 text_of_path))
in {FStar_Ident.ns = ns; FStar_Ident.ident = id; FStar_Ident.nsstr = nsstr; FStar_Ident.str = if (nsstr = "") then begin
id.FStar_Ident.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.FStar_Ident.idText)
end})
end)))

# 393 "FStar.Absyn.Syntax.fst"
let lid_of_path : path  ->  FStar_Range.range  ->  lident = (fun path pos -> (
# 395 "FStar.Absyn.Syntax.fst"
let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

# 396 "FStar.Absyn.Syntax.fst"
let text_of_lid : lident  ->  Prims.string = (fun lid -> lid.FStar_Ident.str)

# 397 "FStar.Absyn.Syntax.fst"
let lid_equals : lident  ->  lident  ->  Prims.bool = (fun l1 l2 -> (l1.FStar_Ident.str = l2.FStar_Ident.str))

# 398 "FStar.Absyn.Syntax.fst"
let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.FStar_Ident.idText = bvd2.realname.FStar_Ident.idText))

# 399 "FStar.Absyn.Syntax.fst"
let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_18_361), FStar_Util.Inr (_18_364)) -> begin
(- (1))
end
| (FStar_Util.Inr (_18_368), FStar_Util.Inl (_18_371)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end))

# 404 "FStar.Absyn.Syntax.fst"
let lid_with_range : lident  ->  FStar_Range.range  ->  lident = (fun lid r -> (
# 407 "FStar.Absyn.Syntax.fst"
let id = (
# 407 "FStar.Absyn.Syntax.fst"
let _18_386 = lid.FStar_Ident.ident
in {FStar_Ident.idText = _18_386.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 408 "FStar.Absyn.Syntax.fst"
let _18_389 = lid
in {FStar_Ident.ns = _18_389.FStar_Ident.ns; FStar_Ident.ident = id; FStar_Ident.nsstr = _18_389.FStar_Ident.nsstr; FStar_Ident.str = _18_389.FStar_Ident.str})))

# 408 "FStar.Absyn.Syntax.fst"
let range_of_lid : lident  ->  FStar_Range.range = (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idRange)

# 409 "FStar.Absyn.Syntax.fst"
let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

# 417 "FStar.Absyn.Syntax.fst"
let syn = (fun p k f -> (f k p))

# 419 "FStar.Absyn.Syntax.fst"
let mk_fvs = (fun _18_400 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 420 "FStar.Absyn.Syntax.fst"
let mk_uvs = (fun _18_401 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 421 "FStar.Absyn.Syntax.fst"
let new_ftv_set = (fun _18_402 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.FStar_Ident.idText y.v.realname.FStar_Ident.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.FStar_Ident.idText)))
end))

# 422 "FStar.Absyn.Syntax.fst"
let new_uv_set = (fun _18_406 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

# 423 "FStar.Absyn.Syntax.fst"
let new_uvt_set = (fun _18_409 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _18_417 _18_421 -> (match ((_18_417, _18_421)) with
| ((x, _18_416), (y, _18_420)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _18_413 -> (match (_18_413) with
| (x, _18_412) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 424 "FStar.Absyn.Syntax.fst"
let no_fvs : freevars = (let _97_1334 = (new_ftv_set ())
in (let _97_1333 = (new_ftv_set ())
in {ftvs = _97_1334; fxvs = _97_1333}))

# 428 "FStar.Absyn.Syntax.fst"
let no_uvs : uvars = (let _97_1337 = (new_uv_set ())
in (let _97_1336 = (new_uvt_set ())
in (let _97_1335 = (new_uvt_set ())
in {uvars_k = _97_1337; uvars_t = _97_1336; uvars_e = _97_1335})))

# 433 "FStar.Absyn.Syntax.fst"
let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 434 "FStar.Absyn.Syntax.fst"
let memo_no_fvs : freevars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_fvs)))

# 435 "FStar.Absyn.Syntax.fst"
let freevars_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  freevars = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _18_1 -> (match (_18_1) with
| FStar_Util.Inl (btv) -> begin
(
# 438 "FStar.Absyn.Syntax.fst"
let _18_427 = out
in (let _97_1342 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _97_1342; fxvs = _18_427.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(
# 439 "FStar.Absyn.Syntax.fst"
let _18_431 = out
in (let _97_1343 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _18_431.ftvs; fxvs = _97_1343}))
end)) no_fvs)))

# 439 "FStar.Absyn.Syntax.fst"
let list_of_freevars : freevars  ->  (btvar, bvvar) FStar_Util.either Prims.list = (fun fvs -> (let _97_1351 = (let _97_1347 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _97_1347 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _97_1350 = (let _97_1349 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _97_1349 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _97_1351 _97_1350))))

# 441 "FStar.Absyn.Syntax.fst"
let get_unit_ref : Prims.unit  ->  Prims.unit Prims.option FStar_ST.ref = (fun _18_436 -> (match (()) with
| () -> begin
(
# 444 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (())))
in (
# 444 "FStar.Absyn.Syntax.fst"
let _18_438 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 444 "FStar.Absyn.Syntax.fst"
let mk_Kind_type : (knd', Prims.unit) syntax = (let _97_1356 = (get_unit_ref ())
in (let _97_1355 = (mk_fvs ())
in (let _97_1354 = (mk_uvs ())
in {n = Kind_type; tk = _97_1356; pos = dummyRange; fvs = _97_1355; uvs = _97_1354})))

# 446 "FStar.Absyn.Syntax.fst"
let mk_Kind_effect : (knd', Prims.unit) syntax = (let _97_1359 = (get_unit_ref ())
in (let _97_1358 = (mk_fvs ())
in (let _97_1357 = (mk_uvs ())
in {n = Kind_effect; tk = _97_1359; pos = dummyRange; fvs = _97_1358; uvs = _97_1357})))

# 447 "FStar.Absyn.Syntax.fst"
let mk_Kind_abbrev : (kabbrev * knd)  ->  FStar_Range.range  ->  knd = (fun _18_442 p -> (match (_18_442) with
| (kabr, k) -> begin
(let _97_1366 = (get_unit_ref ())
in (let _97_1365 = (mk_fvs ())
in (let _97_1364 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _97_1366; pos = p; fvs = _97_1365; uvs = _97_1364})))
end))

# 453 "FStar.Absyn.Syntax.fst"
let mk_Kind_arrow : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _18_446 p -> (match (_18_446) with
| (bs, k) -> begin
(let _97_1373 = (get_unit_ref ())
in (let _97_1372 = (mk_fvs ())
in (let _97_1371 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _97_1373; pos = p; fvs = _97_1372; uvs = _97_1371})))
end))

# 459 "FStar.Absyn.Syntax.fst"
let mk_Kind_arrow' : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _18_450 p -> (match (_18_450) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _18_454 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _18_460 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

# 465 "FStar.Absyn.Syntax.fst"
let mk_Kind_uvar : uvar_k_app  ->  FStar_Range.range  ->  knd = (fun uv p -> (let _97_1384 = (get_unit_ref ())
in (let _97_1383 = (mk_fvs ())
in (let _97_1382 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _97_1384; pos = p; fvs = _97_1383; uvs = _97_1382}))))

# 473 "FStar.Absyn.Syntax.fst"
let mk_Kind_lam : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _18_465 p -> (match (_18_465) with
| (vs, k) -> begin
(let _97_1391 = (get_unit_ref ())
in (let _97_1390 = (mk_fvs ())
in (let _97_1389 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _97_1391; pos = p; fvs = _97_1390; uvs = _97_1389})))
end))

# 479 "FStar.Absyn.Syntax.fst"
let mk_Kind_delayed : (knd * subst_t * knd memo)  ->  FStar_Range.range  ->  knd = (fun _18_470 p -> (match (_18_470) with
| (k, s, m) -> begin
(let _97_1398 = (get_unit_ref ())
in (let _97_1397 = (mk_fvs ())
in (let _97_1396 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _97_1398; pos = p; fvs = _97_1397; uvs = _97_1396})))
end))

# 486 "FStar.Absyn.Syntax.fst"
let mk_Kind_unknown : (knd', Prims.unit) syntax = (let _97_1401 = (get_unit_ref ())
in (let _97_1400 = (mk_fvs ())
in (let _97_1399 = (mk_uvs ())
in {n = Kind_unknown; tk = _97_1401; pos = dummyRange; fvs = _97_1400; uvs = _97_1399})))

# 487 "FStar.Absyn.Syntax.fst"
let get_knd_nref : Prims.unit  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun _18_472 -> (match (()) with
| () -> begin
(
# 490 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (
# 490 "FStar.Absyn.Syntax.fst"
let _18_474 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 490 "FStar.Absyn.Syntax.fst"
let get_knd_ref : (knd', Prims.unit) syntax Prims.option  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun k -> (
# 491 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (
# 491 "FStar.Absyn.Syntax.fst"
let _18_478 = (FStar_ST.op_Colon_Equals x k)
in x)))

# 491 "FStar.Absyn.Syntax.fst"
let mk_Typ_btvar : btvar  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun x k p -> (let _97_1414 = (get_knd_ref k)
in (let _97_1413 = (mk_fvs ())
in (let _97_1412 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _97_1414; pos = p; fvs = _97_1413; uvs = _97_1412}))))

# 493 "FStar.Absyn.Syntax.fst"
let mk_Typ_const : ftvar  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun x k p -> (let _97_1421 = (get_knd_ref k)
in {n = Typ_const (x); tk = _97_1421; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

# 494 "FStar.Absyn.Syntax.fst"
let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _18_491 -> begin
Typ_fun ((bs, c))
end))

# 498 "FStar.Absyn.Syntax.fst"
let mk_Typ_fun : (binders * comp)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_494 k p -> (match (_18_494) with
| (bs, c) -> begin
(let _97_1434 = (check_fun bs c p)
in (let _97_1433 = (FStar_Util.mk_ref k)
in (let _97_1432 = (mk_fvs ())
in (let _97_1431 = (mk_uvs ())
in {n = _97_1434; tk = _97_1433; pos = p; fvs = _97_1432; uvs = _97_1431}))))
end))

# 504 "FStar.Absyn.Syntax.fst"
let mk_Typ_refine : (bvvar * formula)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_499 k p -> (match (_18_499) with
| (x, phi) -> begin
(let _97_1443 = (FStar_Util.mk_ref k)
in (let _97_1442 = (mk_fvs ())
in (let _97_1441 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _97_1443; pos = p; fvs = _97_1442; uvs = _97_1441})))
end))

# 510 "FStar.Absyn.Syntax.fst"
let mk_Typ_app : (typ * args)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_504 k p -> (match (_18_504) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _18_509 -> begin
(let _97_1452 = (FStar_Util.mk_ref k)
in (let _97_1451 = (mk_fvs ())
in (let _97_1450 = (mk_uvs ())
in {n = Typ_app ((t1, args)); tk = _97_1452; pos = p; fvs = _97_1451; uvs = _97_1450})))
end)
end))

# 520 "FStar.Absyn.Syntax.fst"
let mk_Typ_app' : (typ * args)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_512 k p -> (match (_18_512) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _18_517 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

# 524 "FStar.Absyn.Syntax.fst"
let extend_typ_app : (typ * arg)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_520 k p -> (match (_18_520) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _18_528 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

# 527 "FStar.Absyn.Syntax.fst"
let mk_Typ_lam : (binders * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_531 k p -> (match (_18_531) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _18_536 -> begin
(let _97_1473 = (FStar_Util.mk_ref k)
in (let _97_1472 = (mk_fvs ())
in (let _97_1471 = (mk_uvs ())
in {n = Typ_lam ((b, t)); tk = _97_1473; pos = p; fvs = _97_1472; uvs = _97_1471})))
end)
end))

# 537 "FStar.Absyn.Syntax.fst"
let mk_Typ_lam' : (binders * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_539 k p -> (match (_18_539) with
| (bs, t) -> begin
(mk_Typ_lam (bs, t) k p)
end))

# 539 "FStar.Absyn.Syntax.fst"
let mk_Typ_ascribed' : (typ * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_544 k' p -> (match (_18_544) with
| (t, k) -> begin
(let _97_1488 = (FStar_Util.mk_ref k')
in (let _97_1487 = (mk_fvs ())
in (let _97_1486 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _97_1488; pos = p; fvs = _97_1487; uvs = _97_1486})))
end))

# 547 "FStar.Absyn.Syntax.fst"
let mk_Typ_ascribed : (typ * knd)  ->  FStar_Range.range  ->  typ = (fun _18_549 p -> (match (_18_549) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

# 548 "FStar.Absyn.Syntax.fst"
let mk_Typ_meta' : meta_t  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun m k p -> (let _97_1501 = (FStar_Util.mk_ref k)
in (let _97_1500 = (mk_fvs ())
in (let _97_1499 = (mk_uvs ())
in {n = Typ_meta (m); tk = _97_1501; pos = p; fvs = _97_1500; uvs = _97_1499}))))

# 555 "FStar.Absyn.Syntax.fst"
let mk_Typ_meta : meta_t  ->  typ = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _97_1504 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _97_1504 t.pos))
end))

# 561 "FStar.Absyn.Syntax.fst"
let mk_Typ_uvar' : (uvar_t * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_586 k' p -> (match (_18_586) with
| (u, k) -> begin
(let _97_1513 = (get_knd_ref k')
in (let _97_1512 = (mk_fvs ())
in (let _97_1511 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _97_1513; pos = p; fvs = _97_1512; uvs = _97_1511})))
end))

# 569 "FStar.Absyn.Syntax.fst"
let mk_Typ_uvar : (uvar_t * knd)  ->  FStar_Range.range  ->  typ = (fun _18_591 p -> (match (_18_591) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

# 570 "FStar.Absyn.Syntax.fst"
let mk_Typ_delayed : (typ * subst_t * typ memo)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _18_596 k p -> (match (_18_596) with
| (t, s, m) -> begin
(let _97_1533 = (match (t.n) with
| Typ_delayed (_18_600) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _18_603 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _97_1532 = (FStar_Util.mk_ref k)
in (let _97_1531 = (mk_fvs ())
in (let _97_1530 = (mk_uvs ())
in {n = _97_1533; tk = _97_1532; pos = p; fvs = _97_1531; uvs = _97_1530}))))
end))

# 576 "FStar.Absyn.Syntax.fst"
let mk_Typ_delayed' : ((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun st k p -> (let _97_1555 = (let _97_1551 = (let _97_1550 = (FStar_Util.mk_ref None)
in (st, _97_1550))
in Typ_delayed (_97_1551))
in (let _97_1554 = (FStar_Util.mk_ref k)
in (let _97_1553 = (mk_fvs ())
in (let _97_1552 = (mk_uvs ())
in {n = _97_1555; tk = _97_1554; pos = p; fvs = _97_1553; uvs = _97_1552})))))

# 582 "FStar.Absyn.Syntax.fst"
let mk_Typ_unknown : (typ', (knd', Prims.unit) syntax) syntax = (let _97_1558 = (get_knd_nref ())
in (let _97_1557 = (mk_fvs ())
in (let _97_1556 = (mk_uvs ())
in {n = Typ_unknown; tk = _97_1558; pos = dummyRange; fvs = _97_1557; uvs = _97_1556})))

# 584 "FStar.Absyn.Syntax.fst"
let get_typ_nref : Prims.unit  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun _18_607 -> (match (()) with
| () -> begin
(
# 585 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (
# 585 "FStar.Absyn.Syntax.fst"
let _18_609 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 585 "FStar.Absyn.Syntax.fst"
let get_typ_ref : (typ', (knd', Prims.unit) syntax) syntax Prims.option  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun t -> (
# 586 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (
# 586 "FStar.Absyn.Syntax.fst"
let _18_613 = (FStar_ST.op_Colon_Equals x t)
in x)))

# 586 "FStar.Absyn.Syntax.fst"
let mk_Total : typ  ->  comp = (fun t -> (let _97_1567 = (FStar_Util.mk_ref None)
in (let _97_1566 = (mk_fvs ())
in (let _97_1565 = (mk_uvs ())
in {n = Total (t); tk = _97_1567; pos = t.pos; fvs = _97_1566; uvs = _97_1565}))))

# 593 "FStar.Absyn.Syntax.fst"
let mk_Comp : comp_typ  ->  comp = (fun ct -> (let _97_1572 = (FStar_Util.mk_ref None)
in (let _97_1571 = (mk_fvs ())
in (let _97_1570 = (mk_uvs ())
in {n = Comp (ct); tk = _97_1572; pos = ct.result_typ.pos; fvs = _97_1571; uvs = _97_1570}))))

# 599 "FStar.Absyn.Syntax.fst"
let mk_Exp_bvar : bvvar  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun x t p -> (let _97_1581 = (get_typ_ref t)
in (let _97_1580 = (mk_fvs ())
in (let _97_1579 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _97_1581; pos = p; fvs = _97_1580; uvs = _97_1579}))))

# 605 "FStar.Absyn.Syntax.fst"
let mk_Exp_fvar : (fvvar * fv_qual Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_622 t p -> (match (_18_622) with
| (x, b) -> begin
(let _97_1590 = (get_typ_ref t)
in (let _97_1589 = (mk_fvs ())
in (let _97_1588 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _97_1590; pos = p; fvs = _97_1589; uvs = _97_1588})))
end))

# 611 "FStar.Absyn.Syntax.fst"
let mk_Exp_constant : sconst  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun s t p -> (let _97_1599 = (get_typ_ref t)
in (let _97_1598 = (mk_fvs ())
in (let _97_1597 = (mk_uvs ())
in {n = Exp_constant (s); tk = _97_1599; pos = p; fvs = _97_1598; uvs = _97_1597}))))

# 617 "FStar.Absyn.Syntax.fst"
let mk_Exp_abs : (binders * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_630 t' p -> (match (_18_630) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _18_635 -> begin
(let _97_1608 = (get_typ_ref t')
in (let _97_1607 = (mk_fvs ())
in (let _97_1606 = (mk_uvs ())
in {n = Exp_abs ((b, e)); tk = _97_1608; pos = p; fvs = _97_1607; uvs = _97_1606})))
end)
end))

# 626 "FStar.Absyn.Syntax.fst"
let mk_Exp_abs' : (binders * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_638 t' p -> (match (_18_638) with
| (b, e) -> begin
(let _97_1618 = (match ((b, e.n)) with
| (_18_642, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _18_652) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _18_655 -> begin
Exp_abs ((b, e))
end)
in (let _97_1617 = (get_typ_ref t')
in (let _97_1616 = (mk_fvs ())
in (let _97_1615 = (mk_uvs ())
in {n = _97_1618; tk = _97_1617; pos = p; fvs = _97_1616; uvs = _97_1615}))))
end))

# 635 "FStar.Absyn.Syntax.fst"
let mk_Exp_app : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_658 t p -> (match (_18_658) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _18_663 -> begin
(let _97_1627 = (get_typ_ref t)
in (let _97_1626 = (mk_fvs ())
in (let _97_1625 = (mk_uvs ())
in {n = Exp_app ((e1, args)); tk = _97_1627; pos = p; fvs = _97_1626; uvs = _97_1625})))
end)
end))

# 644 "FStar.Absyn.Syntax.fst"
let mk_Exp_app_flat : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_666 t p -> (match (_18_666) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _18_674 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

# 648 "FStar.Absyn.Syntax.fst"
let mk_Exp_app' : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_677 t p -> (match (_18_677) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _18_682 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

# 652 "FStar.Absyn.Syntax.fst"
let rec pat_vars : pat  ->  (btvdef, bvvdef) FStar_Util.either Prims.list = (fun p -> (match (p.v) with
| Pat_cons (_18_685, _18_687, ps) -> begin
(
# 655 "FStar.Absyn.Syntax.fst"
let vars = (FStar_List.collect (fun _18_694 -> (match (_18_694) with
| (x, _18_693) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _18_709 -> begin
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
(
# 665 "FStar.Absyn.Syntax.fst"
let vars = (FStar_List.map pat_vars ps)
in if (not ((let _97_1648 = (FStar_List.tl vars)
in (let _97_1647 = (let _97_1646 = (let _97_1645 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _97_1645))
in (FStar_Util.for_all _97_1646))
in (FStar_All.pipe_right _97_1648 _97_1647))))) then begin
(
# 668 "FStar.Absyn.Syntax.fst"
let vars = (let _97_1652 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _97_1651 = (FStar_List.map (fun _18_2 -> (match (_18_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.FStar_Ident.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idText
end)) v)
in (FStar_Util.concat_l ", " _97_1651)))))
in (FStar_Util.concat_l ";\n" _97_1652))
in (let _97_1655 = (let _97_1654 = (let _97_1653 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_97_1653, p.p))
in Error (_97_1654))
in (Prims.raise _97_1655)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

# 678 "FStar.Absyn.Syntax.fst"
let mk_Exp_match : (exp * (pat * exp Prims.option * exp) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_741 t p -> (match (_18_741) with
| (e, pats) -> begin
(let _97_1664 = (get_typ_ref t)
in (let _97_1663 = (mk_fvs ())
in (let _97_1662 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _97_1664; pos = p; fvs = _97_1663; uvs = _97_1662})))
end))

# 686 "FStar.Absyn.Syntax.fst"
let mk_Exp_ascribed : (exp * typ * lident Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_747 t' p -> (match (_18_747) with
| (e, t, l) -> begin
(let _97_1673 = (get_typ_ref t')
in (let _97_1672 = (mk_fvs ())
in (let _97_1671 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _97_1673; pos = p; fvs = _97_1672; uvs = _97_1671})))
end))

# 692 "FStar.Absyn.Syntax.fst"
let mk_Exp_let : (letbindings * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_752 t p -> (match (_18_752) with
| (lbs, e) -> begin
(let _97_1682 = (get_typ_ref t)
in (let _97_1681 = (mk_fvs ())
in (let _97_1680 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _97_1682; pos = p; fvs = _97_1681; uvs = _97_1680})))
end))

# 699 "FStar.Absyn.Syntax.fst"
let mk_Exp_uvar' : (uvar_e * typ)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_757 t' p -> (match (_18_757) with
| (u, t) -> begin
(let _97_1691 = (get_typ_ref t')
in (let _97_1690 = (mk_fvs ())
in (let _97_1689 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _97_1691; pos = p; fvs = _97_1690; uvs = _97_1689})))
end))

# 707 "FStar.Absyn.Syntax.fst"
let mk_Exp_uvar : (uvar_e * typ)  ->  FStar_Range.range  ->  exp = (fun _18_762 p -> (match (_18_762) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

# 708 "FStar.Absyn.Syntax.fst"
let mk_Exp_delayed : (exp * subst_t * exp memo)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _18_767 t p -> (match (_18_767) with
| (e, s, m) -> begin
(let _97_1704 = (get_typ_ref t)
in (let _97_1703 = (mk_fvs ())
in (let _97_1702 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _97_1704; pos = p; fvs = _97_1703; uvs = _97_1702})))
end))

# 716 "FStar.Absyn.Syntax.fst"
let mk_Exp_meta' : meta_e  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun m t p -> (let _97_1713 = (get_typ_ref t)
in (let _97_1712 = (mk_fvs ())
in (let _97_1711 = (mk_uvs ())
in {n = Exp_meta (m); tk = _97_1713; pos = p; fvs = _97_1712; uvs = _97_1711}))))

# 723 "FStar.Absyn.Syntax.fst"
let mk_Exp_meta : meta_e  ->  exp = (fun m -> (match (m) with
| Meta_desugared (e, _18_776) -> begin
(let _97_1716 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _97_1716 e.pos))
end))

# 725 "FStar.Absyn.Syntax.fst"
let mk_lb : (lbname * lident * typ * exp)  ->  letbinding = (fun _18_783 -> (match (_18_783) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 727 "FStar.Absyn.Syntax.fst"
let mk_subst : subst  ->  subst = (fun s -> s)

# 729 "FStar.Absyn.Syntax.fst"
let extend_subst : (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list = (fun x s -> (x)::s)

# 730 "FStar.Absyn.Syntax.fst"
let argpos : arg  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _18_791) -> begin
t.pos
end
| (FStar_Util.Inr (e), _18_796) -> begin
e.pos
end))

# 733 "FStar.Absyn.Syntax.fst"
let tun : typ = mk_Typ_unknown

# 735 "FStar.Absyn.Syntax.fst"
let kun : knd = mk_Kind_unknown

# 736 "FStar.Absyn.Syntax.fst"
let ktype : knd = mk_Kind_type

# 737 "FStar.Absyn.Syntax.fst"
let keffect : knd = mk_Kind_effect

# 738 "FStar.Absyn.Syntax.fst"
let null_id : ident = (mk_ident ("_", dummyRange))

# 739 "FStar.Absyn.Syntax.fst"
let null_bvd = {ppname = null_id; realname = null_id}

# 740 "FStar.Absyn.Syntax.fst"
let null_bvar = (fun k -> {v = null_bvd; sort = k; p = dummyRange})

# 741 "FStar.Absyn.Syntax.fst"
let t_binder : btvar  ->  binder = (fun a -> (FStar_Util.Inl (a), None))

# 742 "FStar.Absyn.Syntax.fst"
let v_binder : bvvar  ->  binder = (fun a -> (FStar_Util.Inr (a), None))

# 743 "FStar.Absyn.Syntax.fst"
let null_t_binder : knd  ->  binder = (fun t -> (let _97_1735 = (let _97_1734 = (null_bvar t)
in FStar_Util.Inl (_97_1734))
in (_97_1735, None)))

# 744 "FStar.Absyn.Syntax.fst"
let null_v_binder : typ  ->  binder = (fun t -> (let _97_1739 = (let _97_1738 = (null_bvar t)
in FStar_Util.Inr (_97_1738))
in (_97_1739, None)))

# 745 "FStar.Absyn.Syntax.fst"
let itarg : typ  ->  arg = (fun t -> (FStar_Util.Inl (t), Some (Implicit (false))))

# 746 "FStar.Absyn.Syntax.fst"
let ivarg : exp  ->  arg = (fun v -> (FStar_Util.Inr (v), Some (Implicit (false))))

# 747 "FStar.Absyn.Syntax.fst"
let targ : typ  ->  arg = (fun t -> (FStar_Util.Inl (t), None))

# 748 "FStar.Absyn.Syntax.fst"
let varg : exp  ->  arg = (fun v -> (FStar_Util.Inr (v), None))

# 749 "FStar.Absyn.Syntax.fst"
let is_null_pp = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 750 "FStar.Absyn.Syntax.fst"
let is_null_bvd = (fun b -> (b.realname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 751 "FStar.Absyn.Syntax.fst"
let is_null_bvar = (fun b -> (is_null_bvd b.v))

# 752 "FStar.Absyn.Syntax.fst"
let is_null_binder : binder  ->  Prims.bool = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _18_818) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _18_823) -> begin
(is_null_bvar x)
end))

# 755 "FStar.Absyn.Syntax.fst"
let freevars_of_binders : binders  ->  freevars = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _18_3 -> (match (_18_3) with
| (FStar_Util.Inl (btv), _18_831) -> begin
(
# 759 "FStar.Absyn.Syntax.fst"
let _18_833 = out
in (let _97_1760 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _97_1760; fxvs = _18_833.fxvs}))
end
| (FStar_Util.Inr (bxv), _18_838) -> begin
(
# 760 "FStar.Absyn.Syntax.fst"
let _18_840 = out
in (let _97_1761 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _18_840.ftvs; fxvs = _97_1761}))
end)) no_fvs)))

# 760 "FStar.Absyn.Syntax.fst"
let binders_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 762 "FStar.Absyn.Syntax.fst"
let binders_of_freevars : freevars  ->  binders = (fun fvs -> (let _97_1770 = (let _97_1767 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _97_1767 (FStar_List.map t_binder)))
in (let _97_1769 = (let _97_1768 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _97_1768 (FStar_List.map v_binder)))
in (FStar_List.append _97_1770 _97_1769))))

# 764 "FStar.Absyn.Syntax.fst"
let is_implicit : aqual  ->  Prims.bool = (fun _18_4 -> (match (_18_4) with
| Some (Implicit (_18_847)) -> begin
true
end
| _18_851 -> begin
false
end))

# 765 "FStar.Absyn.Syntax.fst"
let as_implicit : Prims.bool  ->  aqual = (fun _18_5 -> (match (_18_5) with
| true -> begin
Some (Implicit (false))
end
| _18_855 -> begin
None
end))




