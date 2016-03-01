
open Prims
# 26 "FStar.Absyn.Syntax.fst"
type ident =
FStar_Ident.ident

# 27 "FStar.Absyn.Syntax.fst"
type lident =
FStar_Ident.lid

# 28 "FStar.Absyn.Syntax.fst"
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
let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_24_7) -> begin
_24_7
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
let ___Error____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (_24_9) -> begin
_24_9
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
let ___Warning____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (_24_11) -> begin
_24_11
end))

# 33 "FStar.Absyn.Syntax.fst"
type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : FStar_Range.range}

# 33 "FStar.Absyn.Syntax.fst"
let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

# 38 "FStar.Absyn.Syntax.fst"
type 't var =
(lident, 't) withinfo_t

# 39 "FStar.Absyn.Syntax.fst"
type fieldname =
lident

# 40 "FStar.Absyn.Syntax.fst"
type 'a bvdef =
{ppname : ident; realname : ident}

# 40 "FStar.Absyn.Syntax.fst"
let is_Mkbvdef = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbvdef"))))

# 41 "FStar.Absyn.Syntax.fst"
type ('a, 't) bvar =
('a bvdef, 't) withinfo_t

# 47 "FStar.Absyn.Syntax.fst"
type sconst =
FStar_Const.sconst

# 48 "FStar.Absyn.Syntax.fst"
type pragma =
| SetOptions of Prims.string
| ResetOptions

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
let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_24_27) -> begin
_24_27
end))

# 51 "FStar.Absyn.Syntax.fst"
type 'a memo =
'a Prims.option FStar_ST.ref

# 52 "FStar.Absyn.Syntax.fst"
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
let ___Implicit____0 : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_24_31) -> begin
_24_31
end))

# 55 "FStar.Absyn.Syntax.fst"
type aqual =
arg_qualifier Prims.option

# 56 "FStar.Absyn.Syntax.fst"
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
let ___Typ_btvar____0 : typ'  ->  btvar = (fun projectee -> (match (projectee) with
| Typ_btvar (_24_55) -> begin
_24_55
end))

# 58 "FStar.Absyn.Syntax.fst"
let ___Typ_const____0 : typ'  ->  ftvar = (fun projectee -> (match (projectee) with
| Typ_const (_24_58) -> begin
_24_58
end))

# 59 "FStar.Absyn.Syntax.fst"
let ___Typ_fun____0 : typ'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Typ_fun (_24_61) -> begin
_24_61
end))

# 60 "FStar.Absyn.Syntax.fst"
let ___Typ_refine____0 : typ'  ->  (bvvar * typ) = (fun projectee -> (match (projectee) with
| Typ_refine (_24_64) -> begin
_24_64
end))

# 61 "FStar.Absyn.Syntax.fst"
let ___Typ_app____0 : typ'  ->  (typ * args) = (fun projectee -> (match (projectee) with
| Typ_app (_24_67) -> begin
_24_67
end))

# 62 "FStar.Absyn.Syntax.fst"
let ___Typ_lam____0 : typ'  ->  (binders * typ) = (fun projectee -> (match (projectee) with
| Typ_lam (_24_70) -> begin
_24_70
end))

# 63 "FStar.Absyn.Syntax.fst"
let ___Typ_ascribed____0 : typ'  ->  (typ * knd) = (fun projectee -> (match (projectee) with
| Typ_ascribed (_24_73) -> begin
_24_73
end))

# 64 "FStar.Absyn.Syntax.fst"
let ___Typ_meta____0 : typ'  ->  meta_t = (fun projectee -> (match (projectee) with
| Typ_meta (_24_76) -> begin
_24_76
end))

# 65 "FStar.Absyn.Syntax.fst"
let ___Typ_uvar____0 : typ'  ->  (uvar_t * knd) = (fun projectee -> (match (projectee) with
| Typ_uvar (_24_79) -> begin
_24_79
end))

# 66 "FStar.Absyn.Syntax.fst"
let ___Typ_delayed____0 : typ'  ->  (((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either * typ memo) = (fun projectee -> (match (projectee) with
| Typ_delayed (_24_82) -> begin
_24_82
end))

# 80 "FStar.Absyn.Syntax.fst"
let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_24_86) -> begin
_24_86
end))

# 81 "FStar.Absyn.Syntax.fst"
let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_24_89) -> begin
_24_89
end))

# 90 "FStar.Absyn.Syntax.fst"
let ___DECREASES____0 : cflags  ->  exp = (fun projectee -> (match (projectee) with
| DECREASES (_24_92) -> begin
_24_92
end))

# 93 "FStar.Absyn.Syntax.fst"
let ___Meta_pattern____0 : meta_t  ->  (typ * arg Prims.list Prims.list) = (fun projectee -> (match (projectee) with
| Meta_pattern (_24_95) -> begin
_24_95
end))

# 94 "FStar.Absyn.Syntax.fst"
let ___Meta_named____0 : meta_t  ->  (typ * lident) = (fun projectee -> (match (projectee) with
| Meta_named (_24_98) -> begin
_24_98
end))

# 95 "FStar.Absyn.Syntax.fst"
let ___Meta_labeled____0 : meta_t  ->  (typ * Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_24_101) -> begin
_24_101
end))

# 96 "FStar.Absyn.Syntax.fst"
let ___Meta_refresh_label____0 : meta_t  ->  (typ * Prims.bool Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta_refresh_label (_24_104) -> begin
_24_104
end))

# 97 "FStar.Absyn.Syntax.fst"
let ___Meta_slack_formula____0 : meta_t  ->  (typ * typ * Prims.bool FStar_ST.ref) = (fun projectee -> (match (projectee) with
| Meta_slack_formula (_24_107) -> begin
_24_107
end))

# 100 "FStar.Absyn.Syntax.fst"
let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_24_110) -> begin
_24_110
end))

# 102 "FStar.Absyn.Syntax.fst"
let ___Exp_bvar____0 : exp'  ->  bvvar = (fun projectee -> (match (projectee) with
| Exp_bvar (_24_113) -> begin
_24_113
end))

# 103 "FStar.Absyn.Syntax.fst"
let ___Exp_fvar____0 : exp'  ->  (fvvar * fv_qual Prims.option) = (fun projectee -> (match (projectee) with
| Exp_fvar (_24_116) -> begin
_24_116
end))

# 104 "FStar.Absyn.Syntax.fst"
let ___Exp_constant____0 : exp'  ->  sconst = (fun projectee -> (match (projectee) with
| Exp_constant (_24_119) -> begin
_24_119
end))

# 105 "FStar.Absyn.Syntax.fst"
let ___Exp_abs____0 : exp'  ->  (binders * exp) = (fun projectee -> (match (projectee) with
| Exp_abs (_24_122) -> begin
_24_122
end))

# 106 "FStar.Absyn.Syntax.fst"
let ___Exp_app____0 : exp'  ->  (exp * args) = (fun projectee -> (match (projectee) with
| Exp_app (_24_125) -> begin
_24_125
end))

# 107 "FStar.Absyn.Syntax.fst"
let ___Exp_match____0 : exp'  ->  (exp * (pat * exp Prims.option * exp) Prims.list) = (fun projectee -> (match (projectee) with
| Exp_match (_24_128) -> begin
_24_128
end))

# 108 "FStar.Absyn.Syntax.fst"
let ___Exp_ascribed____0 : exp'  ->  (exp * typ * lident Prims.option) = (fun projectee -> (match (projectee) with
| Exp_ascribed (_24_131) -> begin
_24_131
end))

# 109 "FStar.Absyn.Syntax.fst"
let ___Exp_let____0 : exp'  ->  (letbindings * exp) = (fun projectee -> (match (projectee) with
| Exp_let (_24_134) -> begin
_24_134
end))

# 110 "FStar.Absyn.Syntax.fst"
let ___Exp_uvar____0 : exp'  ->  (uvar_e * typ) = (fun projectee -> (match (projectee) with
| Exp_uvar (_24_137) -> begin
_24_137
end))

# 111 "FStar.Absyn.Syntax.fst"
let ___Exp_delayed____0 : exp'  ->  (exp * subst_t * exp memo) = (fun projectee -> (match (projectee) with
| Exp_delayed (_24_140) -> begin
_24_140
end))

# 112 "FStar.Absyn.Syntax.fst"
let ___Exp_meta____0 : exp'  ->  meta_e = (fun projectee -> (match (projectee) with
| Exp_meta (_24_143) -> begin
_24_143
end))

# 115 "FStar.Absyn.Syntax.fst"
let ___Meta_desugared____0 : meta_e  ->  (exp * meta_source_info) = (fun projectee -> (match (projectee) with
| Meta_desugared (_24_145) -> begin
_24_145
end))

# 124 "FStar.Absyn.Syntax.fst"
let ___Record_projector____0 : fv_qual  ->  lident = (fun projectee -> (match (projectee) with
| Record_projector (_24_148) -> begin
_24_148
end))

# 125 "FStar.Absyn.Syntax.fst"
let ___Record_ctor____0 : fv_qual  ->  (lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_24_151) -> begin
_24_151
end))

# 130 "FStar.Absyn.Syntax.fst"
let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_24_154) -> begin
_24_154
end))

# 131 "FStar.Absyn.Syntax.fst"
let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_24_157) -> begin
_24_157
end))

# 132 "FStar.Absyn.Syntax.fst"
let ___Pat_cons____0 : pat'  ->  (fvvar * fv_qual Prims.option * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_24_160) -> begin
_24_160
end))

# 133 "FStar.Absyn.Syntax.fst"
let ___Pat_var____0 : pat'  ->  bvvar = (fun projectee -> (match (projectee) with
| Pat_var (_24_163) -> begin
_24_163
end))

# 134 "FStar.Absyn.Syntax.fst"
let ___Pat_tvar____0 : pat'  ->  btvar = (fun projectee -> (match (projectee) with
| Pat_tvar (_24_166) -> begin
_24_166
end))

# 135 "FStar.Absyn.Syntax.fst"
let ___Pat_wild____0 : pat'  ->  bvvar = (fun projectee -> (match (projectee) with
| Pat_wild (_24_169) -> begin
_24_169
end))

# 136 "FStar.Absyn.Syntax.fst"
let ___Pat_twild____0 : pat'  ->  btvar = (fun projectee -> (match (projectee) with
| Pat_twild (_24_172) -> begin
_24_172
end))

# 137 "FStar.Absyn.Syntax.fst"
let ___Pat_dot_term____0 : pat'  ->  (bvvar * exp) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_24_175) -> begin
_24_175
end))

# 138 "FStar.Absyn.Syntax.fst"
let ___Pat_dot_typ____0 : pat'  ->  (btvar * typ) = (fun projectee -> (match (projectee) with
| Pat_dot_typ (_24_178) -> begin
_24_178
end))

# 143 "FStar.Absyn.Syntax.fst"
let ___Kind_abbrev____0 : knd'  ->  (kabbrev * knd) = (fun projectee -> (match (projectee) with
| Kind_abbrev (_24_181) -> begin
_24_181
end))

# 144 "FStar.Absyn.Syntax.fst"
let ___Kind_arrow____0 : knd'  ->  (binders * knd) = (fun projectee -> (match (projectee) with
| Kind_arrow (_24_184) -> begin
_24_184
end))

# 145 "FStar.Absyn.Syntax.fst"
let ___Kind_uvar____0 : knd'  ->  uvar_k_app = (fun projectee -> (match (projectee) with
| Kind_uvar (_24_187) -> begin
_24_187
end))

# 146 "FStar.Absyn.Syntax.fst"
let ___Kind_lam____0 : knd'  ->  (binders * knd) = (fun projectee -> (match (projectee) with
| Kind_lam (_24_190) -> begin
_24_190
end))

# 147 "FStar.Absyn.Syntax.fst"
let ___Kind_delayed____0 : knd'  ->  (knd * subst_t * knd memo) = (fun projectee -> (match (projectee) with
| Kind_delayed (_24_193) -> begin
_24_193
end))

# 186 "FStar.Absyn.Syntax.fst"
type subst =
subst_elt Prims.list

# 187 "FStar.Absyn.Syntax.fst"
type either_var =
(btvar, bvvar) FStar_Util.either

# 188 "FStar.Absyn.Syntax.fst"
type freevars_l =
either_var Prims.list

# 189 "FStar.Absyn.Syntax.fst"
type formula =
typ

# 190 "FStar.Absyn.Syntax.fst"
type formulae =
typ Prims.list

# 191 "FStar.Absyn.Syntax.fst"
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
let ___Discriminator____0 : qualifier  ->  lident = (fun projectee -> (match (projectee) with
| Discriminator (_24_200) -> begin
_24_200
end))

# 199 "FStar.Absyn.Syntax.fst"
let ___Projector____0 : qualifier  ->  (lident * (btvdef, bvvdef) FStar_Util.either) = (fun projectee -> (match (projectee) with
| Projector (_24_203) -> begin
_24_203
end))

# 200 "FStar.Absyn.Syntax.fst"
let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_24_206) -> begin
_24_206
end))

# 201 "FStar.Absyn.Syntax.fst"
let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_24_209) -> begin
_24_209
end))

# 203 "FStar.Absyn.Syntax.fst"
let ___DefaultEffect____0 : qualifier  ->  lident Prims.option = (fun projectee -> (match (projectee) with
| DefaultEffect (_24_212) -> begin
_24_212
end))

# 208 "FStar.Absyn.Syntax.fst"
type tycon =
(lident * binders * knd)

# 209 "FStar.Absyn.Syntax.fst"
type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

# 209 "FStar.Absyn.Syntax.fst"
let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

# 214 "FStar.Absyn.Syntax.fst"
type sub_eff =
{source : lident; target : lident; lift : typ}

# 214 "FStar.Absyn.Syntax.fst"
let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

# 219 "FStar.Absyn.Syntax.fst"
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
let ___Sig_tycon____0 : sigelt  ->  (lident * binders * knd * lident Prims.list * lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_tycon (_24_242) -> begin
_24_242
end))

# 241 "FStar.Absyn.Syntax.fst"
let ___Sig_kind_abbrev____0 : sigelt  ->  (lident * binders * knd * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_kind_abbrev (_24_245) -> begin
_24_245
end))

# 242 "FStar.Absyn.Syntax.fst"
let ___Sig_typ_abbrev____0 : sigelt  ->  (lident * binders * knd * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_typ_abbrev (_24_248) -> begin
_24_248
end))

# 243 "FStar.Absyn.Syntax.fst"
let ___Sig_datacon____0 : sigelt  ->  (lident * typ * tycon * qualifier Prims.list * lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_24_251) -> begin
_24_251
end))

# 244 "FStar.Absyn.Syntax.fst"
let ___Sig_val_decl____0 : sigelt  ->  (lident * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_val_decl (_24_254) -> begin
_24_254
end))

# 245 "FStar.Absyn.Syntax.fst"
let ___Sig_assume____0 : sigelt  ->  (lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_24_257) -> begin
_24_257
end))

# 246 "FStar.Absyn.Syntax.fst"
let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_24_260) -> begin
_24_260
end))

# 247 "FStar.Absyn.Syntax.fst"
let ___Sig_main____0 : sigelt  ->  (exp * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_24_263) -> begin
_24_263
end))

# 248 "FStar.Absyn.Syntax.fst"
let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_24_266) -> begin
_24_266
end))

# 249 "FStar.Absyn.Syntax.fst"
let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_24_269) -> begin
_24_269
end))

# 250 "FStar.Absyn.Syntax.fst"
let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_24_272) -> begin
_24_272
end))

# 251 "FStar.Absyn.Syntax.fst"
let ___Sig_effect_abbrev____0 : sigelt  ->  (lident * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_24_275) -> begin
_24_275
end))

# 252 "FStar.Absyn.Syntax.fst"
let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_24_278) -> begin
_24_278
end))

# 253 "FStar.Absyn.Syntax.fst"
type sigelts =
sigelt Prims.list

# 255 "FStar.Absyn.Syntax.fst"
type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool; is_deserialized : Prims.bool}

# 255 "FStar.Absyn.Syntax.fst"
let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

# 263 "FStar.Absyn.Syntax.fst"
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
let ___K____0 : ktec  ->  knd = (fun projectee -> (match (projectee) with
| K (_24_287) -> begin
_24_287
end))

# 265 "FStar.Absyn.Syntax.fst"
let ___T____0 : ktec  ->  (typ * knd Prims.option) = (fun projectee -> (match (projectee) with
| T (_24_290) -> begin
_24_290
end))

# 266 "FStar.Absyn.Syntax.fst"
let ___E____0 : ktec  ->  exp = (fun projectee -> (match (projectee) with
| E (_24_293) -> begin
_24_293
end))

# 267 "FStar.Absyn.Syntax.fst"
let ___C____0 : ktec  ->  comp = (fun projectee -> (match (projectee) with
| C (_24_296) -> begin
_24_296
end))

# 269 "FStar.Absyn.Syntax.fst"
type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags Prims.list; comp : Prims.unit  ->  comp}

# 269 "FStar.Absyn.Syntax.fst"
let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

# 275 "FStar.Absyn.Syntax.fst"
type path =
Prims.string Prims.list

# 376 "FStar.Absyn.Syntax.fst"
let dummyRange : FStar_Range.range = 0L

# 377 "FStar.Absyn.Syntax.fst"
let withinfo = (fun v s r -> {v = v; sort = s; p = r})

# 378 "FStar.Absyn.Syntax.fst"
let withsort = (fun v s -> (withinfo v s dummyRange))

# 379 "FStar.Absyn.Syntax.fst"
let mk_ident : (Prims.string * FStar_Range.range)  ->  ident = (fun _24_332 -> (match (_24_332) with
| (text, range) -> begin
{FStar_Ident.idText = text; FStar_Ident.idRange = range}
end))

# 380 "FStar.Absyn.Syntax.fst"
let id_of_text : Prims.string  ->  ident = (fun str -> (mk_ident (str, dummyRange)))

# 381 "FStar.Absyn.Syntax.fst"
let text_of_id : ident  ->  Prims.string = (fun id -> id.FStar_Ident.idText)

# 382 "FStar.Absyn.Syntax.fst"
let text_of_path : path  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))

# 383 "FStar.Absyn.Syntax.fst"
let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))

# 384 "FStar.Absyn.Syntax.fst"
let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))

# 385 "FStar.Absyn.Syntax.fst"
let path_of_lid : lident  ->  path = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))

# 386 "FStar.Absyn.Syntax.fst"
let ids_of_lid : lident  ->  ident Prims.list = (fun lid -> (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[])))

# 387 "FStar.Absyn.Syntax.fst"
let lid_of_ids : ident Prims.list  ->  lident = (fun ids -> (
# 388 "FStar.Absyn.Syntax.fst"
let _24_343 = (FStar_Util.prefix ids)
in (match (_24_343) with
| (ns, id) -> begin
(
# 389 "FStar.Absyn.Syntax.fst"
let nsstr = (let _105_1272 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _105_1272 text_of_path))
in {FStar_Ident.ns = ns; FStar_Ident.ident = id; FStar_Ident.nsstr = nsstr; FStar_Ident.str = if (nsstr = "") then begin
id.FStar_Ident.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.FStar_Ident.idText)
end})
end)))

# 394 "FStar.Absyn.Syntax.fst"
let lid_of_path : path  ->  FStar_Range.range  ->  lident = (fun path pos -> (
# 395 "FStar.Absyn.Syntax.fst"
let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

# 397 "FStar.Absyn.Syntax.fst"
let text_of_lid : lident  ->  Prims.string = (fun lid -> lid.FStar_Ident.str)

# 398 "FStar.Absyn.Syntax.fst"
let lid_equals : lident  ->  lident  ->  Prims.bool = (fun l1 l2 -> (l1.FStar_Ident.str = l2.FStar_Ident.str))

# 399 "FStar.Absyn.Syntax.fst"
let bvd_eq = (fun bvd1 bvd2 -> (bvd1.realname.FStar_Ident.idText = bvd2.realname.FStar_Ident.idText))

# 400 "FStar.Absyn.Syntax.fst"
let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_24_358), FStar_Util.Inr (_24_361)) -> begin
(- (1))
end
| (FStar_Util.Inr (_24_365), FStar_Util.Inl (_24_368)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.realname.FStar_Ident.idText y.realname.FStar_Ident.idText)
end))

# 406 "FStar.Absyn.Syntax.fst"
let lid_with_range : lident  ->  FStar_Range.range  ->  lident = (fun lid r -> (
# 407 "FStar.Absyn.Syntax.fst"
let id = (
# 407 "FStar.Absyn.Syntax.fst"
let _24_383 = lid.FStar_Ident.ident
in {FStar_Ident.idText = _24_383.FStar_Ident.idText; FStar_Ident.idRange = r})
in (
# 408 "FStar.Absyn.Syntax.fst"
let _24_386 = lid
in {FStar_Ident.ns = _24_386.FStar_Ident.ns; FStar_Ident.ident = id; FStar_Ident.nsstr = _24_386.FStar_Ident.nsstr; FStar_Ident.str = _24_386.FStar_Ident.str})))

# 409 "FStar.Absyn.Syntax.fst"
let range_of_lid : lident  ->  FStar_Range.range = (fun lid -> lid.FStar_Ident.ident.FStar_Ident.idRange)

# 410 "FStar.Absyn.Syntax.fst"
let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(range_of_lid l)
end))

# 419 "FStar.Absyn.Syntax.fst"
let syn = (fun p k f -> (f k p))

# 420 "FStar.Absyn.Syntax.fst"
let mk_fvs = (fun _24_397 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 421 "FStar.Absyn.Syntax.fst"
let mk_uvs = (fun _24_398 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 422 "FStar.Absyn.Syntax.fst"
let new_ftv_set = (fun _24_399 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> (FStar_Util.compare x.v.realname.FStar_Ident.idText y.v.realname.FStar_Ident.idText)) (fun x -> (FStar_Util.hashcode x.v.realname.FStar_Ident.idText)))
end))

# 423 "FStar.Absyn.Syntax.fst"
let new_uv_set = (fun _24_403 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) FStar_Unionfind.uvar_id)
end))

# 424 "FStar.Absyn.Syntax.fst"
let new_uvt_set = (fun _24_406 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _24_414 _24_418 -> (match ((_24_414, _24_418)) with
| ((x, _24_413), (y, _24_417)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _24_410 -> (match (_24_410) with
| (x, _24_409) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 425 "FStar.Absyn.Syntax.fst"
let no_fvs : freevars = (let _105_1321 = (new_ftv_set ())
in (let _105_1320 = (new_ftv_set ())
in {ftvs = _105_1321; fxvs = _105_1320}))

# 429 "FStar.Absyn.Syntax.fst"
let no_uvs : uvars = (let _105_1324 = (new_uv_set ())
in (let _105_1323 = (new_uvt_set ())
in (let _105_1322 = (new_uvt_set ())
in {uvars_k = _105_1324; uvars_t = _105_1323; uvars_e = _105_1322})))

# 434 "FStar.Absyn.Syntax.fst"
let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 435 "FStar.Absyn.Syntax.fst"
let memo_no_fvs : freevars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_fvs)))

# 436 "FStar.Absyn.Syntax.fst"
let freevars_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  freevars = (fun l -> (FStar_All.pipe_right l (FStar_List.fold_left (fun out _24_1 -> (match (_24_1) with
| FStar_Util.Inl (btv) -> begin
(
# 438 "FStar.Absyn.Syntax.fst"
let _24_424 = out
in (let _105_1329 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _105_1329; fxvs = _24_424.fxvs}))
end
| FStar_Util.Inr (bxv) -> begin
(
# 439 "FStar.Absyn.Syntax.fst"
let _24_428 = out
in (let _105_1330 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _24_428.ftvs; fxvs = _105_1330}))
end)) no_fvs)))

# 440 "FStar.Absyn.Syntax.fst"
let list_of_freevars : freevars  ->  (btvar, bvvar) FStar_Util.either Prims.list = (fun fvs -> (let _105_1338 = (let _105_1334 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _105_1334 (FStar_List.map (fun x -> FStar_Util.Inl (x)))))
in (let _105_1337 = (let _105_1336 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _105_1336 (FStar_List.map (fun x -> FStar_Util.Inr (x)))))
in (FStar_List.append _105_1338 _105_1337))))

# 444 "FStar.Absyn.Syntax.fst"
let get_unit_ref : Prims.unit  ->  Prims.unit Prims.option FStar_ST.ref = (fun _24_433 -> (match (()) with
| () -> begin
(
# 444 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (())))
in (
# 444 "FStar.Absyn.Syntax.fst"
let _24_435 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 446 "FStar.Absyn.Syntax.fst"
let mk_Kind_type : (knd', Prims.unit) syntax = (let _105_1343 = (get_unit_ref ())
in (let _105_1342 = (mk_fvs ())
in (let _105_1341 = (mk_uvs ())
in {n = Kind_type; tk = _105_1343; pos = dummyRange; fvs = _105_1342; uvs = _105_1341})))

# 447 "FStar.Absyn.Syntax.fst"
let mk_Kind_effect : (knd', Prims.unit) syntax = (let _105_1346 = (get_unit_ref ())
in (let _105_1345 = (mk_fvs ())
in (let _105_1344 = (mk_uvs ())
in {n = Kind_effect; tk = _105_1346; pos = dummyRange; fvs = _105_1345; uvs = _105_1344})))

# 448 "FStar.Absyn.Syntax.fst"
let mk_Kind_abbrev : (kabbrev * knd)  ->  FStar_Range.range  ->  knd = (fun _24_439 p -> (match (_24_439) with
| (kabr, k) -> begin
(let _105_1353 = (get_unit_ref ())
in (let _105_1352 = (mk_fvs ())
in (let _105_1351 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _105_1353; pos = p; fvs = _105_1352; uvs = _105_1351})))
end))

# 454 "FStar.Absyn.Syntax.fst"
let mk_Kind_arrow : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _24_443 p -> (match (_24_443) with
| (bs, k) -> begin
(let _105_1360 = (get_unit_ref ())
in (let _105_1359 = (mk_fvs ())
in (let _105_1358 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _105_1360; pos = p; fvs = _105_1359; uvs = _105_1358})))
end))

# 460 "FStar.Absyn.Syntax.fst"
let mk_Kind_arrow' : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _24_447 p -> (match (_24_447) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _24_451 -> begin
(match (k.n) with
| Kind_arrow (bs', k') -> begin
(mk_Kind_arrow ((FStar_List.append bs bs'), k') p)
end
| _24_457 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

# 467 "FStar.Absyn.Syntax.fst"
let mk_Kind_uvar : uvar_k_app  ->  FStar_Range.range  ->  knd = (fun uv p -> (let _105_1371 = (get_unit_ref ())
in (let _105_1370 = (mk_fvs ())
in (let _105_1369 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _105_1371; pos = p; fvs = _105_1370; uvs = _105_1369}))))

# 474 "FStar.Absyn.Syntax.fst"
let mk_Kind_lam : (binders * knd)  ->  FStar_Range.range  ->  knd = (fun _24_462 p -> (match (_24_462) with
| (vs, k) -> begin
(let _105_1378 = (get_unit_ref ())
in (let _105_1377 = (mk_fvs ())
in (let _105_1376 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _105_1378; pos = p; fvs = _105_1377; uvs = _105_1376})))
end))

# 480 "FStar.Absyn.Syntax.fst"
let mk_Kind_delayed : (knd * subst_t * knd memo)  ->  FStar_Range.range  ->  knd = (fun _24_467 p -> (match (_24_467) with
| (k, s, m) -> begin
(let _105_1385 = (get_unit_ref ())
in (let _105_1384 = (mk_fvs ())
in (let _105_1383 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _105_1385; pos = p; fvs = _105_1384; uvs = _105_1383})))
end))

# 487 "FStar.Absyn.Syntax.fst"
let mk_Kind_unknown : (knd', Prims.unit) syntax = (let _105_1388 = (get_unit_ref ())
in (let _105_1387 = (mk_fvs ())
in (let _105_1386 = (mk_uvs ())
in {n = Kind_unknown; tk = _105_1388; pos = dummyRange; fvs = _105_1387; uvs = _105_1386})))

# 490 "FStar.Absyn.Syntax.fst"
let get_knd_nref : Prims.unit  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun _24_469 -> (match (()) with
| () -> begin
(
# 490 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (
# 490 "FStar.Absyn.Syntax.fst"
let _24_471 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 491 "FStar.Absyn.Syntax.fst"
let get_knd_ref : (knd', Prims.unit) syntax Prims.option  ->  (knd', Prims.unit) syntax Prims.option FStar_ST.ref = (fun k -> (
# 491 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Kind_unknown)))
in (
# 491 "FStar.Absyn.Syntax.fst"
let _24_475 = (FStar_ST.op_Colon_Equals x k)
in x)))

# 493 "FStar.Absyn.Syntax.fst"
let mk_Typ_btvar : btvar  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun x k p -> (let _105_1401 = (get_knd_ref k)
in (let _105_1400 = (mk_fvs ())
in (let _105_1399 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _105_1401; pos = p; fvs = _105_1400; uvs = _105_1399}))))

# 494 "FStar.Absyn.Syntax.fst"
let mk_Typ_const : ftvar  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun x k p -> (let _105_1408 = (get_knd_ref k)
in {n = Typ_const (x); tk = _105_1408; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

# 495 "FStar.Absyn.Syntax.fst"
let rec check_fun = (fun bs c p -> (match (bs) with
| [] -> begin
(FStar_All.failwith "Empty binders")
end
| _24_488 -> begin
Typ_fun ((bs, c))
end))

# 499 "FStar.Absyn.Syntax.fst"
let mk_Typ_fun : (binders * comp)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_491 k p -> (match (_24_491) with
| (bs, c) -> begin
(let _105_1421 = (check_fun bs c p)
in (let _105_1420 = (FStar_Util.mk_ref k)
in (let _105_1419 = (mk_fvs ())
in (let _105_1418 = (mk_uvs ())
in {n = _105_1421; tk = _105_1420; pos = p; fvs = _105_1419; uvs = _105_1418}))))
end))

# 505 "FStar.Absyn.Syntax.fst"
let mk_Typ_refine : (bvvar * formula)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_496 k p -> (match (_24_496) with
| (x, phi) -> begin
(let _105_1430 = (FStar_Util.mk_ref k)
in (let _105_1429 = (mk_fvs ())
in (let _105_1428 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _105_1430; pos = p; fvs = _105_1429; uvs = _105_1428})))
end))

# 511 "FStar.Absyn.Syntax.fst"
let mk_Typ_app : (typ * args)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_501 k p -> (match (_24_501) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _24_506 -> begin
(let _105_1439 = (FStar_Util.mk_ref k)
in (let _105_1438 = (mk_fvs ())
in (let _105_1437 = (mk_uvs ())
in {n = Typ_app ((t1, args)); tk = _105_1439; pos = p; fvs = _105_1438; uvs = _105_1437})))
end)
end))

# 521 "FStar.Absyn.Syntax.fst"
let mk_Typ_app' : (typ * args)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_509 k p -> (match (_24_509) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _24_514 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

# 525 "FStar.Absyn.Syntax.fst"
let extend_typ_app : (typ * arg)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_517 k p -> (match (_24_517) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app (h, args) -> begin
(mk_Typ_app (h, (FStar_List.append args ((arg)::[]))) k p)
end
| _24_525 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

# 528 "FStar.Absyn.Syntax.fst"
let mk_Typ_lam : (binders * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_528 k p -> (match (_24_528) with
| (b, t) -> begin
(match (b) with
| [] -> begin
t
end
| _24_533 -> begin
(let _105_1460 = (FStar_Util.mk_ref k)
in (let _105_1459 = (mk_fvs ())
in (let _105_1458 = (mk_uvs ())
in {n = Typ_lam ((b, t)); tk = _105_1460; pos = p; fvs = _105_1459; uvs = _105_1458})))
end)
end))

# 538 "FStar.Absyn.Syntax.fst"
let mk_Typ_lam' : (binders * typ)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_536 k p -> (match (_24_536) with
| (bs, t) -> begin
(mk_Typ_lam (bs, t) k p)
end))

# 541 "FStar.Absyn.Syntax.fst"
let mk_Typ_ascribed' : (typ * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_541 k' p -> (match (_24_541) with
| (t, k) -> begin
(let _105_1475 = (FStar_Util.mk_ref k')
in (let _105_1474 = (mk_fvs ())
in (let _105_1473 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _105_1475; pos = p; fvs = _105_1474; uvs = _105_1473})))
end))

# 548 "FStar.Absyn.Syntax.fst"
let mk_Typ_ascribed : (typ * knd)  ->  FStar_Range.range  ->  typ = (fun _24_546 p -> (match (_24_546) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

# 550 "FStar.Absyn.Syntax.fst"
let mk_Typ_meta' : meta_t  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun m k p -> (let _105_1488 = (FStar_Util.mk_ref k)
in (let _105_1487 = (mk_fvs ())
in (let _105_1486 = (mk_uvs ())
in {n = Typ_meta (m); tk = _105_1488; pos = p; fvs = _105_1487; uvs = _105_1486}))))

# 556 "FStar.Absyn.Syntax.fst"
let mk_Typ_meta : meta_t  ->  typ = (fun m -> (match (m) with
| (Meta_pattern (t, _)) | (Meta_named (t, _)) | (Meta_labeled (t, _, _, _)) | (Meta_refresh_label (t, _, _)) | (Meta_slack_formula (t, _, _)) -> begin
(let _105_1491 = (FStar_ST.read t.tk)
in (mk_Typ_meta' m _105_1491 t.pos))
end))

# 563 "FStar.Absyn.Syntax.fst"
let mk_Typ_uvar' : (uvar_t * knd)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_583 k' p -> (match (_24_583) with
| (u, k) -> begin
(let _105_1500 = (get_knd_ref k')
in (let _105_1499 = (mk_fvs ())
in (let _105_1498 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _105_1500; pos = p; fvs = _105_1499; uvs = _105_1498})))
end))

# 570 "FStar.Absyn.Syntax.fst"
let mk_Typ_uvar : (uvar_t * knd)  ->  FStar_Range.range  ->  typ = (fun _24_588 p -> (match (_24_588) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

# 571 "FStar.Absyn.Syntax.fst"
let mk_Typ_delayed : (typ * subst_t * typ memo)  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun _24_593 k p -> (match (_24_593) with
| (t, s, m) -> begin
(let _105_1520 = (match (t.n) with
| Typ_delayed (_24_597) -> begin
(FStar_All.failwith "NESTED DELAYED TYPES!")
end
| _24_600 -> begin
Typ_delayed ((FStar_Util.Inl ((t, s)), m))
end)
in (let _105_1519 = (FStar_Util.mk_ref k)
in (let _105_1518 = (mk_fvs ())
in (let _105_1517 = (mk_uvs ())
in {n = _105_1520; tk = _105_1519; pos = p; fvs = _105_1518; uvs = _105_1517}))))
end))

# 577 "FStar.Absyn.Syntax.fst"
let mk_Typ_delayed' : ((typ * subst_t), Prims.unit  ->  typ) FStar_Util.either  ->  knd Prims.option  ->  FStar_Range.range  ->  typ = (fun st k p -> (let _105_1542 = (let _105_1538 = (let _105_1537 = (FStar_Util.mk_ref None)
in (st, _105_1537))
in Typ_delayed (_105_1538))
in (let _105_1541 = (FStar_Util.mk_ref k)
in (let _105_1540 = (mk_fvs ())
in (let _105_1539 = (mk_uvs ())
in {n = _105_1542; tk = _105_1541; pos = p; fvs = _105_1540; uvs = _105_1539})))))

# 584 "FStar.Absyn.Syntax.fst"
let mk_Typ_unknown : (typ', (knd', Prims.unit) syntax) syntax = (let _105_1545 = (get_knd_nref ())
in (let _105_1544 = (mk_fvs ())
in (let _105_1543 = (mk_uvs ())
in {n = Typ_unknown; tk = _105_1545; pos = dummyRange; fvs = _105_1544; uvs = _105_1543})))

# 585 "FStar.Absyn.Syntax.fst"
let get_typ_nref : Prims.unit  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun _24_604 -> (match (()) with
| () -> begin
(
# 585 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (
# 585 "FStar.Absyn.Syntax.fst"
let _24_606 = (FStar_ST.op_Colon_Equals x None)
in x))
end))

# 586 "FStar.Absyn.Syntax.fst"
let get_typ_ref : (typ', (knd', Prims.unit) syntax) syntax Prims.option  ->  (typ', (knd', Prims.unit) syntax) syntax Prims.option FStar_ST.ref = (fun t -> (
# 586 "FStar.Absyn.Syntax.fst"
let x = (FStar_Util.mk_ref (Some (mk_Typ_unknown)))
in (
# 586 "FStar.Absyn.Syntax.fst"
let _24_610 = (FStar_ST.op_Colon_Equals x t)
in x)))

# 588 "FStar.Absyn.Syntax.fst"
let mk_Total : typ  ->  comp = (fun t -> (let _105_1554 = (FStar_Util.mk_ref None)
in (let _105_1553 = (mk_fvs ())
in (let _105_1552 = (mk_uvs ())
in {n = Total (t); tk = _105_1554; pos = t.pos; fvs = _105_1553; uvs = _105_1552}))))

# 594 "FStar.Absyn.Syntax.fst"
let mk_Comp : comp_typ  ->  comp = (fun ct -> (let _105_1559 = (FStar_Util.mk_ref None)
in (let _105_1558 = (mk_fvs ())
in (let _105_1557 = (mk_uvs ())
in {n = Comp (ct); tk = _105_1559; pos = ct.result_typ.pos; fvs = _105_1558; uvs = _105_1557}))))

# 600 "FStar.Absyn.Syntax.fst"
let mk_Exp_bvar : bvvar  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun x t p -> (let _105_1568 = (get_typ_ref t)
in (let _105_1567 = (mk_fvs ())
in (let _105_1566 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _105_1568; pos = p; fvs = _105_1567; uvs = _105_1566}))))

# 606 "FStar.Absyn.Syntax.fst"
let mk_Exp_fvar : (fvvar * fv_qual Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_619 t p -> (match (_24_619) with
| (x, b) -> begin
(let _105_1577 = (get_typ_ref t)
in (let _105_1576 = (mk_fvs ())
in (let _105_1575 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _105_1577; pos = p; fvs = _105_1576; uvs = _105_1575})))
end))

# 612 "FStar.Absyn.Syntax.fst"
let mk_Exp_constant : sconst  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun s t p -> (let _105_1586 = (get_typ_ref t)
in (let _105_1585 = (mk_fvs ())
in (let _105_1584 = (mk_uvs ())
in {n = Exp_constant (s); tk = _105_1586; pos = p; fvs = _105_1585; uvs = _105_1584}))))

# 618 "FStar.Absyn.Syntax.fst"
let mk_Exp_abs : (binders * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_627 t' p -> (match (_24_627) with
| (b, e) -> begin
(match (b) with
| [] -> begin
e
end
| _24_632 -> begin
(let _105_1595 = (get_typ_ref t')
in (let _105_1594 = (mk_fvs ())
in (let _105_1593 = (mk_uvs ())
in {n = Exp_abs ((b, e)); tk = _105_1595; pos = p; fvs = _105_1594; uvs = _105_1593})))
end)
end))

# 627 "FStar.Absyn.Syntax.fst"
let mk_Exp_abs' : (binders * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_635 t' p -> (match (_24_635) with
| (b, e) -> begin
(let _105_1605 = (match ((b, e.n)) with
| (_24_639, Exp_abs (b0::bs, body)) -> begin
Exp_abs (((FStar_List.append b ((b0)::bs)), body))
end
| ([], _24_649) -> begin
(FStar_All.failwith "abstraction with no binders!")
end
| _24_652 -> begin
Exp_abs ((b, e))
end)
in (let _105_1604 = (get_typ_ref t')
in (let _105_1603 = (mk_fvs ())
in (let _105_1602 = (mk_uvs ())
in {n = _105_1605; tk = _105_1604; pos = p; fvs = _105_1603; uvs = _105_1602}))))
end))

# 636 "FStar.Absyn.Syntax.fst"
let mk_Exp_app : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_655 t p -> (match (_24_655) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _24_660 -> begin
(let _105_1614 = (get_typ_ref t)
in (let _105_1613 = (mk_fvs ())
in (let _105_1612 = (mk_uvs ())
in {n = Exp_app ((e1, args)); tk = _105_1614; pos = p; fvs = _105_1613; uvs = _105_1612})))
end)
end))

# 645 "FStar.Absyn.Syntax.fst"
let mk_Exp_app_flat : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_663 t p -> (match (_24_663) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app (e1', args') -> begin
(mk_Exp_app (e1', (FStar_List.append args' args)) t p)
end
| _24_671 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

# 649 "FStar.Absyn.Syntax.fst"
let mk_Exp_app' : (exp * args)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_674 t p -> (match (_24_674) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _24_679 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

# 653 "FStar.Absyn.Syntax.fst"
let rec pat_vars : pat  ->  (btvdef, bvvdef) FStar_Util.either Prims.list = (fun p -> (match (p.v) with
| Pat_cons (_24_682, _24_684, ps) -> begin
(
# 655 "FStar.Absyn.Syntax.fst"
let vars = (FStar_List.collect (fun _24_691 -> (match (_24_691) with
| (x, _24_690) -> begin
(pat_vars x)
end)) ps)
in if (FStar_All.pipe_right vars (FStar_Util.nodups (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _24_706 -> begin
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
in if (not ((let _105_1635 = (FStar_List.tl vars)
in (let _105_1634 = (let _105_1633 = (let _105_1632 = (FStar_List.hd vars)
in (FStar_Util.set_eq order_bvd _105_1632))
in (FStar_Util.for_all _105_1633))
in (FStar_All.pipe_right _105_1635 _105_1634))))) then begin
(
# 668 "FStar.Absyn.Syntax.fst"
let vars = (let _105_1639 = (FStar_All.pipe_right vars (FStar_List.map (fun v -> (let _105_1638 = (FStar_List.map (fun _24_2 -> (match (_24_2) with
| FStar_Util.Inr (x) -> begin
x.ppname.FStar_Ident.idText
end
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idText
end)) v)
in (FStar_Util.concat_l ", " _105_1638)))))
in (FStar_Util.concat_l ";\n" _105_1639))
in (let _105_1642 = (let _105_1641 = (let _105_1640 = (FStar_Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_105_1640, p.p))
in Error (_105_1641))
in (Prims.raise _105_1642)))
end else begin
(FStar_List.hd vars)
end)
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

# 680 "FStar.Absyn.Syntax.fst"
let mk_Exp_match : (exp * (pat * exp Prims.option * exp) Prims.list)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_738 t p -> (match (_24_738) with
| (e, pats) -> begin
(let _105_1651 = (get_typ_ref t)
in (let _105_1650 = (mk_fvs ())
in (let _105_1649 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _105_1651; pos = p; fvs = _105_1650; uvs = _105_1649})))
end))

# 687 "FStar.Absyn.Syntax.fst"
let mk_Exp_ascribed : (exp * typ * lident Prims.option)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_744 t' p -> (match (_24_744) with
| (e, t, l) -> begin
(let _105_1660 = (get_typ_ref t')
in (let _105_1659 = (mk_fvs ())
in (let _105_1658 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _105_1660; pos = p; fvs = _105_1659; uvs = _105_1658})))
end))

# 693 "FStar.Absyn.Syntax.fst"
let mk_Exp_let : (letbindings * exp)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_749 t p -> (match (_24_749) with
| (lbs, e) -> begin
(let _105_1669 = (get_typ_ref t)
in (let _105_1668 = (mk_fvs ())
in (let _105_1667 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _105_1669; pos = p; fvs = _105_1668; uvs = _105_1667})))
end))

# 701 "FStar.Absyn.Syntax.fst"
let mk_Exp_uvar' : (uvar_e * typ)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_754 t' p -> (match (_24_754) with
| (u, t) -> begin
(let _105_1678 = (get_typ_ref t')
in (let _105_1677 = (mk_fvs ())
in (let _105_1676 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _105_1678; pos = p; fvs = _105_1677; uvs = _105_1676})))
end))

# 708 "FStar.Absyn.Syntax.fst"
let mk_Exp_uvar : (uvar_e * typ)  ->  FStar_Range.range  ->  exp = (fun _24_759 p -> (match (_24_759) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

# 710 "FStar.Absyn.Syntax.fst"
let mk_Exp_delayed : (exp * subst_t * exp memo)  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun _24_764 t p -> (match (_24_764) with
| (e, s, m) -> begin
(let _105_1691 = (get_typ_ref t)
in (let _105_1690 = (mk_fvs ())
in (let _105_1689 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _105_1691; pos = p; fvs = _105_1690; uvs = _105_1689})))
end))

# 717 "FStar.Absyn.Syntax.fst"
let mk_Exp_meta' : meta_e  ->  typ Prims.option  ->  FStar_Range.range  ->  exp = (fun m t p -> (let _105_1700 = (get_typ_ref t)
in (let _105_1699 = (mk_fvs ())
in (let _105_1698 = (mk_uvs ())
in {n = Exp_meta (m); tk = _105_1700; pos = p; fvs = _105_1699; uvs = _105_1698}))))

# 724 "FStar.Absyn.Syntax.fst"
let mk_Exp_meta : meta_e  ->  exp = (fun m -> (match (m) with
| Meta_desugared (e, _24_773) -> begin
(let _105_1703 = (FStar_ST.read e.tk)
in (mk_Exp_meta' m _105_1703 e.pos))
end))

# 727 "FStar.Absyn.Syntax.fst"
let mk_lb : (lbname * lident * typ * exp)  ->  letbinding = (fun _24_780 -> (match (_24_780) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 729 "FStar.Absyn.Syntax.fst"
let mk_subst : subst  ->  subst = (fun s -> s)

# 730 "FStar.Absyn.Syntax.fst"
let extend_subst : (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list  ->  (((typ', (knd', Prims.unit) syntax) syntax bvdef * (typ', (knd', Prims.unit) syntax) syntax), ((exp', (typ', (knd', Prims.unit) syntax) syntax) syntax bvdef * (exp', (typ', (knd', Prims.unit) syntax) syntax) syntax)) FStar_Util.either Prims.list = (fun x s -> (x)::s)

# 731 "FStar.Absyn.Syntax.fst"
let argpos : arg  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Util.Inl (t), _24_788) -> begin
t.pos
end
| (FStar_Util.Inr (e), _24_793) -> begin
e.pos
end))

# 735 "FStar.Absyn.Syntax.fst"
let tun : typ = mk_Typ_unknown

# 736 "FStar.Absyn.Syntax.fst"
let kun : knd = mk_Kind_unknown

# 737 "FStar.Absyn.Syntax.fst"
let ktype : knd = mk_Kind_type

# 738 "FStar.Absyn.Syntax.fst"
let keffect : knd = mk_Kind_effect

# 739 "FStar.Absyn.Syntax.fst"
let null_id : ident = (mk_ident ("_", dummyRange))

# 740 "FStar.Absyn.Syntax.fst"
let null_bvd = {ppname = null_id; realname = null_id}

# 741 "FStar.Absyn.Syntax.fst"
let null_bvar = (fun k -> {v = null_bvd; sort = k; p = dummyRange})

# 742 "FStar.Absyn.Syntax.fst"
let t_binder : btvar  ->  binder = (fun a -> (FStar_Util.Inl (a), None))

# 743 "FStar.Absyn.Syntax.fst"
let v_binder : bvvar  ->  binder = (fun a -> (FStar_Util.Inr (a), None))

# 744 "FStar.Absyn.Syntax.fst"
let null_t_binder : knd  ->  binder = (fun t -> (let _105_1722 = (let _105_1721 = (null_bvar t)
in FStar_Util.Inl (_105_1721))
in (_105_1722, None)))

# 745 "FStar.Absyn.Syntax.fst"
let null_v_binder : typ  ->  binder = (fun t -> (let _105_1726 = (let _105_1725 = (null_bvar t)
in FStar_Util.Inr (_105_1725))
in (_105_1726, None)))

# 746 "FStar.Absyn.Syntax.fst"
let itarg : typ  ->  arg = (fun t -> (FStar_Util.Inl (t), Some (Implicit (false))))

# 747 "FStar.Absyn.Syntax.fst"
let ivarg : exp  ->  arg = (fun v -> (FStar_Util.Inr (v), Some (Implicit (false))))

# 748 "FStar.Absyn.Syntax.fst"
let targ : typ  ->  arg = (fun t -> (FStar_Util.Inl (t), None))

# 749 "FStar.Absyn.Syntax.fst"
let varg : exp  ->  arg = (fun v -> (FStar_Util.Inr (v), None))

# 750 "FStar.Absyn.Syntax.fst"
let is_null_pp = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 751 "FStar.Absyn.Syntax.fst"
let is_null_bvd = (fun b -> (b.realname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 752 "FStar.Absyn.Syntax.fst"
let is_null_bvar = (fun b -> (is_null_bvd b.v))

# 753 "FStar.Absyn.Syntax.fst"
let is_null_binder : binder  ->  Prims.bool = (fun b -> (match (b) with
| (FStar_Util.Inl (a), _24_815) -> begin
(is_null_bvar a)
end
| (FStar_Util.Inr (x), _24_820) -> begin
(is_null_bvar x)
end))

# 757 "FStar.Absyn.Syntax.fst"
let freevars_of_binders : binders  ->  freevars = (fun bs -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun out _24_3 -> (match (_24_3) with
| (FStar_Util.Inl (btv), _24_828) -> begin
(
# 759 "FStar.Absyn.Syntax.fst"
let _24_830 = out
in (let _105_1747 = (FStar_Util.set_add btv out.ftvs)
in {ftvs = _105_1747; fxvs = _24_830.fxvs}))
end
| (FStar_Util.Inr (bxv), _24_835) -> begin
(
# 760 "FStar.Absyn.Syntax.fst"
let _24_837 = out
in (let _105_1748 = (FStar_Util.set_add bxv out.fxvs)
in {ftvs = _24_837.ftvs; fxvs = _105_1748}))
end)) no_fvs)))

# 762 "FStar.Absyn.Syntax.fst"
let binders_of_list : (btvar, bvvar) FStar_Util.either Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 763 "FStar.Absyn.Syntax.fst"
let binders_of_freevars : freevars  ->  binders = (fun fvs -> (let _105_1757 = (let _105_1754 = (FStar_Util.set_elements fvs.ftvs)
in (FStar_All.pipe_right _105_1754 (FStar_List.map t_binder)))
in (let _105_1756 = (let _105_1755 = (FStar_Util.set_elements fvs.fxvs)
in (FStar_All.pipe_right _105_1755 (FStar_List.map v_binder)))
in (FStar_List.append _105_1757 _105_1756))))

# 765 "FStar.Absyn.Syntax.fst"
let is_implicit : aqual  ->  Prims.bool = (fun _24_4 -> (match (_24_4) with
| Some (Implicit (_24_844)) -> begin
true
end
| _24_848 -> begin
false
end))

# 766 "FStar.Absyn.Syntax.fst"
let as_implicit : Prims.bool  ->  aqual = (fun _24_5 -> (match (_24_5) with
| true -> begin
Some (Implicit (false))
end
| _24_852 -> begin
None
end))




