
open Prims
# 28 "FStar.Syntax.Syntax.fst"
exception Err of (Prims.string)

# 28 "FStar.Syntax.Syntax.fst"
let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Syntax.Syntax.fst"
let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_29_7) -> begin
_29_7
end))

# 29 "FStar.Syntax.Syntax.fst"
exception Error of ((Prims.string * FStar_Range.range))

# 29 "FStar.Syntax.Syntax.fst"
let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Syntax.Syntax.fst"
let ___Error____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (_29_9) -> begin
_29_9
end))

# 30 "FStar.Syntax.Syntax.fst"
exception Warning of ((Prims.string * FStar_Range.range))

# 30 "FStar.Syntax.Syntax.fst"
let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Syntax.Syntax.fst"
let ___Warning____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (_29_11) -> begin
_29_11
end))

# 33 "FStar.Syntax.Syntax.fst"
type ('a, 't) withinfo_t =
{v : 'a; ty : 't; p : FStar_Range.range}

# 33 "FStar.Syntax.Syntax.fst"
let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

# 40 "FStar.Syntax.Syntax.fst"
type 't var =
(FStar_Ident.lident, 't) withinfo_t

# 41 "FStar.Syntax.Syntax.fst"
type fieldname =
FStar_Ident.lident

# 43 "FStar.Syntax.Syntax.fst"
type sconst =
FStar_Const.sconst

# 45 "FStar.Syntax.Syntax.fst"
type pragma =
| SetOptions of Prims.string
| ResetOptions

# 46 "FStar.Syntax.Syntax.fst"
let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Syntax.Syntax.fst"
let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Syntax.Syntax.fst"
let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_29_21) -> begin
_29_21
end))

# 49 "FStar.Syntax.Syntax.fst"
type 'a memo =
'a Prims.option FStar_ST.ref

# 51 "FStar.Syntax.Syntax.fst"
type arg_qualifier =
| Implicit of Prims.bool
| Equality

# 52 "FStar.Syntax.Syntax.fst"
let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.Syntax.Syntax.fst"
let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Syntax.Syntax.fst"
let ___Implicit____0 : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit (_29_25) -> begin
_29_25
end))

# 54 "FStar.Syntax.Syntax.fst"
type aqual =
arg_qualifier Prims.option

# 55 "FStar.Syntax.Syntax.fst"
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

# 56 "FStar.Syntax.Syntax.fst"
let is_U_zero = (fun _discr_ -> (match (_discr_) with
| U_zero (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Syntax.Syntax.fst"
let is_U_succ = (fun _discr_ -> (match (_discr_) with
| U_succ (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.Syntax.Syntax.fst"
let is_U_max = (fun _discr_ -> (match (_discr_) with
| U_max (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.Syntax.Syntax.fst"
let is_U_bvar = (fun _discr_ -> (match (_discr_) with
| U_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.Syntax.Syntax.fst"
let is_U_name = (fun _discr_ -> (match (_discr_) with
| U_name (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.Syntax.Syntax.fst"
let is_U_unif = (fun _discr_ -> (match (_discr_) with
| U_unif (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.Syntax.Syntax.fst"
let is_U_unknown = (fun _discr_ -> (match (_discr_) with
| U_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Syntax.Syntax.fst"
let ___U_succ____0 : universe  ->  universe = (fun projectee -> (match (projectee) with
| U_succ (_29_28) -> begin
_29_28
end))

# 58 "FStar.Syntax.Syntax.fst"
let ___U_max____0 : universe  ->  universe Prims.list = (fun projectee -> (match (projectee) with
| U_max (_29_31) -> begin
_29_31
end))

# 59 "FStar.Syntax.Syntax.fst"
let ___U_bvar____0 : universe  ->  Prims.int = (fun projectee -> (match (projectee) with
| U_bvar (_29_34) -> begin
_29_34
end))

# 60 "FStar.Syntax.Syntax.fst"
let ___U_name____0 : universe  ->  univ_name = (fun projectee -> (match (projectee) with
| U_name (_29_37) -> begin
_29_37
end))

# 61 "FStar.Syntax.Syntax.fst"
let ___U_unif____0 : universe  ->  universe Prims.option FStar_Unionfind.uvar = (fun projectee -> (match (projectee) with
| U_unif (_29_40) -> begin
_29_40
end))

# 65 "FStar.Syntax.Syntax.fst"
type universe_uvar =
universe Prims.option FStar_Unionfind.uvar

# 66 "FStar.Syntax.Syntax.fst"
type univ_names =
univ_name Prims.list

# 67 "FStar.Syntax.Syntax.fst"
type universes =
universe Prims.list

# 69 "FStar.Syntax.Syntax.fst"
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
| DB of (Prims.int * bv)
| NM of (bv * Prims.int)
| NT of (bv * term)
| UN of (Prims.int * universe)
| UD of (univ_name * Prims.int) 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : FStar_Range.range; vars : free_vars memo} 
 and bv =
{ppname : FStar_Ident.ident; index : Prims.int; sort : term} 
 and free_vars =
{free_names : bv FStar_Util.set; free_uvars : uvars; free_univs : universe_uvar FStar_Util.set} 
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

# 70 "FStar.Syntax.Syntax.fst"
let is_Tm_bvar = (fun _discr_ -> (match (_discr_) with
| Tm_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.Syntax.Syntax.fst"
let is_Tm_name = (fun _discr_ -> (match (_discr_) with
| Tm_name (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Syntax.Syntax.fst"
let is_Tm_fvar = (fun _discr_ -> (match (_discr_) with
| Tm_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Syntax.Syntax.fst"
let is_Tm_uinst = (fun _discr_ -> (match (_discr_) with
| Tm_uinst (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Syntax.Syntax.fst"
let is_Tm_constant = (fun _discr_ -> (match (_discr_) with
| Tm_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "FStar.Syntax.Syntax.fst"
let is_Tm_type = (fun _discr_ -> (match (_discr_) with
| Tm_type (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "FStar.Syntax.Syntax.fst"
let is_Tm_abs = (fun _discr_ -> (match (_discr_) with
| Tm_abs (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "FStar.Syntax.Syntax.fst"
let is_Tm_arrow = (fun _discr_ -> (match (_discr_) with
| Tm_arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.Syntax.Syntax.fst"
let is_Tm_refine = (fun _discr_ -> (match (_discr_) with
| Tm_refine (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.Syntax.Syntax.fst"
let is_Tm_app = (fun _discr_ -> (match (_discr_) with
| Tm_app (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.Syntax.Syntax.fst"
let is_Tm_match = (fun _discr_ -> (match (_discr_) with
| Tm_match (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.Syntax.Syntax.fst"
let is_Tm_ascribed = (fun _discr_ -> (match (_discr_) with
| Tm_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.Syntax.Syntax.fst"
let is_Tm_let = (fun _discr_ -> (match (_discr_) with
| Tm_let (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.Syntax.Syntax.fst"
let is_Tm_uvar = (fun _discr_ -> (match (_discr_) with
| Tm_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.Syntax.Syntax.fst"
let is_Tm_delayed = (fun _discr_ -> (match (_discr_) with
| Tm_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Syntax.Syntax.fst"
let is_Tm_meta = (fun _discr_ -> (match (_discr_) with
| Tm_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Syntax.Syntax.fst"
let is_Tm_unknown = (fun _discr_ -> (match (_discr_) with
| Tm_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Syntax.Syntax.fst"
let is_Pat_constant = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.Syntax.Syntax.fst"
let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "FStar.Syntax.Syntax.fst"
let is_Pat_cons = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "FStar.Syntax.Syntax.fst"
let is_Pat_var = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "FStar.Syntax.Syntax.fst"
let is_Pat_wild = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "FStar.Syntax.Syntax.fst"
let is_Pat_dot_term = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

# 96 "FStar.Syntax.Syntax.fst"
let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

# 103 "FStar.Syntax.Syntax.fst"
let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

# 110 "FStar.Syntax.Syntax.fst"
let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Syntax.Syntax.fst"
let is_GTotal = (fun _discr_ -> (match (_discr_) with
| GTotal (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "FStar.Syntax.Syntax.fst"
let is_Comp = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "FStar.Syntax.Syntax.fst"
let is_TOTAL = (fun _discr_ -> (match (_discr_) with
| TOTAL (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "FStar.Syntax.Syntax.fst"
let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT (_) -> begin
true
end
| _ -> begin
false
end))

# 124 "FStar.Syntax.Syntax.fst"
let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 125 "FStar.Syntax.Syntax.fst"
let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 126 "FStar.Syntax.Syntax.fst"
let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "FStar.Syntax.Syntax.fst"
let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "FStar.Syntax.Syntax.fst"
let is_DECREASES = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

# 131 "FStar.Syntax.Syntax.fst"
let is_Meta_pattern = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "FStar.Syntax.Syntax.fst"
let is_Meta_named = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.Syntax.Syntax.fst"
let is_Meta_labeled = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "FStar.Syntax.Syntax.fst"
let is_Meta_desugared = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.Syntax.Syntax.fst"
let is_Uvar = (fun _ _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 137 "FStar.Syntax.Syntax.fst"
let is_Fixed = (fun _ _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

# 139 "FStar.Syntax.Syntax.fst"
let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app (_) -> begin
true
end
| _ -> begin
false
end))

# 140 "FStar.Syntax.Syntax.fst"
let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "FStar.Syntax.Syntax.fst"
let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "FStar.Syntax.Syntax.fst"
let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "FStar.Syntax.Syntax.fst"
let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "FStar.Syntax.Syntax.fst"
let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "FStar.Syntax.Syntax.fst"
let is_Record_projector = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "FStar.Syntax.Syntax.fst"
let is_Record_ctor = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 152 "FStar.Syntax.Syntax.fst"
let is_DB = (fun _discr_ -> (match (_discr_) with
| DB (_) -> begin
true
end
| _ -> begin
false
end))

# 153 "FStar.Syntax.Syntax.fst"
let is_NM = (fun _discr_ -> (match (_discr_) with
| NM (_) -> begin
true
end
| _ -> begin
false
end))

# 154 "FStar.Syntax.Syntax.fst"
let is_NT = (fun _discr_ -> (match (_discr_) with
| NT (_) -> begin
true
end
| _ -> begin
false
end))

# 155 "FStar.Syntax.Syntax.fst"
let is_UN = (fun _discr_ -> (match (_discr_) with
| UN (_) -> begin
true
end
| _ -> begin
false
end))

# 156 "FStar.Syntax.Syntax.fst"
let is_UD = (fun _discr_ -> (match (_discr_) with
| UD (_) -> begin
true
end
| _ -> begin
false
end))

# 159 "FStar.Syntax.Syntax.fst"
let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

# 165 "FStar.Syntax.Syntax.fst"
let is_Mkbv : bv  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbv"))))

# 171 "FStar.Syntax.Syntax.fst"
let is_Mkfree_vars : free_vars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfree_vars"))))

# 176 "FStar.Syntax.Syntax.fst"
let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

# 70 "FStar.Syntax.Syntax.fst"
let ___Tm_bvar____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_bvar (_29_69) -> begin
_29_69
end))

# 71 "FStar.Syntax.Syntax.fst"
let ___Tm_name____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_name (_29_72) -> begin
_29_72
end))

# 72 "FStar.Syntax.Syntax.fst"
let ___Tm_fvar____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| Tm_fvar (_29_75) -> begin
_29_75
end))

# 73 "FStar.Syntax.Syntax.fst"
let ___Tm_uinst____0 : term'  ->  (term * universes) = (fun projectee -> (match (projectee) with
| Tm_uinst (_29_78) -> begin
_29_78
end))

# 74 "FStar.Syntax.Syntax.fst"
let ___Tm_constant____0 : term'  ->  sconst = (fun projectee -> (match (projectee) with
| Tm_constant (_29_81) -> begin
_29_81
end))

# 75 "FStar.Syntax.Syntax.fst"
let ___Tm_type____0 : term'  ->  universe = (fun projectee -> (match (projectee) with
| Tm_type (_29_84) -> begin
_29_84
end))

# 76 "FStar.Syntax.Syntax.fst"
let ___Tm_abs____0 : term'  ->  (binders * term * lcomp Prims.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_29_87) -> begin
_29_87
end))

# 77 "FStar.Syntax.Syntax.fst"
let ___Tm_arrow____0 : term'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Tm_arrow (_29_90) -> begin
_29_90
end))

# 78 "FStar.Syntax.Syntax.fst"
let ___Tm_refine____0 : term'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Tm_refine (_29_93) -> begin
_29_93
end))

# 79 "FStar.Syntax.Syntax.fst"
let ___Tm_app____0 : term'  ->  (term * args) = (fun projectee -> (match (projectee) with
| Tm_app (_29_96) -> begin
_29_96
end))

# 80 "FStar.Syntax.Syntax.fst"
let ___Tm_match____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_29_99) -> begin
_29_99
end))

# 81 "FStar.Syntax.Syntax.fst"
let ___Tm_ascribed____0 : term'  ->  (term * term * FStar_Ident.lident Prims.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_29_102) -> begin
_29_102
end))

# 82 "FStar.Syntax.Syntax.fst"
let ___Tm_let____0 : term'  ->  (letbindings * term) = (fun projectee -> (match (projectee) with
| Tm_let (_29_105) -> begin
_29_105
end))

# 83 "FStar.Syntax.Syntax.fst"
let ___Tm_uvar____0 : term'  ->  (uvar * term) = (fun projectee -> (match (projectee) with
| Tm_uvar (_29_108) -> begin
_29_108
end))

# 84 "FStar.Syntax.Syntax.fst"
let ___Tm_delayed____0 : term'  ->  (((term * subst_ts), Prims.unit  ->  term) FStar_Util.either * term memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_29_111) -> begin
_29_111
end))

# 86 "FStar.Syntax.Syntax.fst"
let ___Tm_meta____0 : term'  ->  (term * metadata) = (fun projectee -> (match (projectee) with
| Tm_meta (_29_114) -> begin
_29_114
end))

# 90 "FStar.Syntax.Syntax.fst"
let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_29_117) -> begin
_29_117
end))

# 91 "FStar.Syntax.Syntax.fst"
let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_29_120) -> begin
_29_120
end))

# 92 "FStar.Syntax.Syntax.fst"
let ___Pat_cons____0 : pat'  ->  (fv * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_29_123) -> begin
_29_123
end))

# 93 "FStar.Syntax.Syntax.fst"
let ___Pat_var____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_var (_29_126) -> begin
_29_126
end))

# 94 "FStar.Syntax.Syntax.fst"
let ___Pat_wild____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_wild (_29_129) -> begin
_29_129
end))

# 95 "FStar.Syntax.Syntax.fst"
let ___Pat_dot_term____0 : pat'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_29_132) -> begin
_29_132
end))

# 110 "FStar.Syntax.Syntax.fst"
let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_29_137) -> begin
_29_137
end))

# 111 "FStar.Syntax.Syntax.fst"
let ___GTotal____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| GTotal (_29_140) -> begin
_29_140
end))

# 112 "FStar.Syntax.Syntax.fst"
let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_29_143) -> begin
_29_143
end))

# 128 "FStar.Syntax.Syntax.fst"
let ___DECREASES____0 : cflags  ->  term = (fun projectee -> (match (projectee) with
| DECREASES (_29_146) -> begin
_29_146
end))

# 131 "FStar.Syntax.Syntax.fst"
let ___Meta_pattern____0 : metadata  ->  args Prims.list = (fun projectee -> (match (projectee) with
| Meta_pattern (_29_149) -> begin
_29_149
end))

# 132 "FStar.Syntax.Syntax.fst"
let ___Meta_named____0 : metadata  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Meta_named (_29_152) -> begin
_29_152
end))

# 133 "FStar.Syntax.Syntax.fst"
let ___Meta_labeled____0 : metadata  ->  (Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_29_155) -> begin
_29_155
end))

# 134 "FStar.Syntax.Syntax.fst"
let ___Meta_desugared____0 : metadata  ->  meta_source_info = (fun projectee -> (match (projectee) with
| Meta_desugared (_29_158) -> begin
_29_158
end))

# 137 "FStar.Syntax.Syntax.fst"
let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_29_161) -> begin
_29_161
end))

# 146 "FStar.Syntax.Syntax.fst"
let ___Record_projector____0 : fv_qual  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Record_projector (_29_164) -> begin
_29_164
end))

# 147 "FStar.Syntax.Syntax.fst"
let ___Record_ctor____0 : fv_qual  ->  (FStar_Ident.lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_29_167) -> begin
_29_167
end))

# 152 "FStar.Syntax.Syntax.fst"
let ___DB____0 : subst_elt  ->  (Prims.int * bv) = (fun projectee -> (match (projectee) with
| DB (_29_170) -> begin
_29_170
end))

# 153 "FStar.Syntax.Syntax.fst"
let ___NM____0 : subst_elt  ->  (bv * Prims.int) = (fun projectee -> (match (projectee) with
| NM (_29_173) -> begin
_29_173
end))

# 154 "FStar.Syntax.Syntax.fst"
let ___NT____0 : subst_elt  ->  (bv * term) = (fun projectee -> (match (projectee) with
| NT (_29_176) -> begin
_29_176
end))

# 155 "FStar.Syntax.Syntax.fst"
let ___UN____0 : subst_elt  ->  (Prims.int * universe) = (fun projectee -> (match (projectee) with
| UN (_29_179) -> begin
_29_179
end))

# 156 "FStar.Syntax.Syntax.fst"
let ___UD____0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_29_182) -> begin
_29_182
end))

# 183 "FStar.Syntax.Syntax.fst"
type tscheme =
(univ_name Prims.list * typ)

# 185 "FStar.Syntax.Syntax.fst"
type freenames_l =
bv Prims.list

# 186 "FStar.Syntax.Syntax.fst"
type formula =
typ

# 187 "FStar.Syntax.Syntax.fst"
type formulae =
typ Prims.list

# 188 "FStar.Syntax.Syntax.fst"
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

# 189 "FStar.Syntax.Syntax.fst"
let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 190 "FStar.Syntax.Syntax.fst"
let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 191 "FStar.Syntax.Syntax.fst"
let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 192 "FStar.Syntax.Syntax.fst"
let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))

# 193 "FStar.Syntax.Syntax.fst"
let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable (_) -> begin
true
end
| _ -> begin
false
end))

# 194 "FStar.Syntax.Syntax.fst"
let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))

# 195 "FStar.Syntax.Syntax.fst"
let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 196 "FStar.Syntax.Syntax.fst"
let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 197 "FStar.Syntax.Syntax.fst"
let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 199 "FStar.Syntax.Syntax.fst"
let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 200 "FStar.Syntax.Syntax.fst"
let is_Discriminator = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

# 201 "FStar.Syntax.Syntax.fst"
let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

# 202 "FStar.Syntax.Syntax.fst"
let is_RecordType = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

# 203 "FStar.Syntax.Syntax.fst"
let is_RecordConstructor = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 204 "FStar.Syntax.Syntax.fst"
let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 205 "FStar.Syntax.Syntax.fst"
let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 206 "FStar.Syntax.Syntax.fst"
let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 196 "FStar.Syntax.Syntax.fst"
let ___DefaultEffect____0 : qualifier  ->  FStar_Ident.lident Prims.option = (fun projectee -> (match (projectee) with
| DefaultEffect (_29_189) -> begin
_29_189
end))

# 200 "FStar.Syntax.Syntax.fst"
let ___Discriminator____0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Discriminator (_29_192) -> begin
_29_192
end))

# 201 "FStar.Syntax.Syntax.fst"
let ___Projector____0 : qualifier  ->  (FStar_Ident.lident * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_29_195) -> begin
_29_195
end))

# 202 "FStar.Syntax.Syntax.fst"
let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_29_198) -> begin
_29_198
end))

# 203 "FStar.Syntax.Syntax.fst"
let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_29_201) -> begin
_29_201
end))

# 208 "FStar.Syntax.Syntax.fst"
type tycon =
(FStar_Ident.lident * binders * typ)

# 209 "FStar.Syntax.Syntax.fst"
type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}

# 209 "FStar.Syntax.Syntax.fst"
let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

# 214 "FStar.Syntax.Syntax.fst"
type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift : tscheme}

# 214 "FStar.Syntax.Syntax.fst"
let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

# 219 "FStar.Syntax.Syntax.fst"
type eff_decl =
{qualifiers : qualifier Prims.list; mname : FStar_Ident.lident; univs : univ_names; binders : binders; signature : term; ret : tscheme; bind_wp : tscheme; bind_wlp : tscheme; if_then_else : tscheme; ite_wp : tscheme; ite_wlp : tscheme; wp_binop : tscheme; wp_as_type : tscheme; close_wp : tscheme; assert_p : tscheme; assume_p : tscheme; null_wp : tscheme; trivial : tscheme} 
 and sigelt =
| Sig_inductive_typ of (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range)
| Sig_bundle of (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_datacon of (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range)
| Sig_declare_typ of (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range)
| Sig_let of (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list)
| Sig_main of (term * FStar_Range.range)
| Sig_assume of (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range)
| Sig_new_effect of (eff_decl * FStar_Range.range)
| Sig_sub_effect of (sub_eff * FStar_Range.range)
| Sig_effect_abbrev of (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range)
| Sig_pragma of (pragma * FStar_Range.range)

# 219 "FStar.Syntax.Syntax.fst"
let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

# 240 "FStar.Syntax.Syntax.fst"
let is_Sig_inductive_typ = (fun _discr_ -> (match (_discr_) with
| Sig_inductive_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 253 "FStar.Syntax.Syntax.fst"
let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

# 257 "FStar.Syntax.Syntax.fst"
let is_Sig_datacon = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

# 265 "FStar.Syntax.Syntax.fst"
let is_Sig_declare_typ = (fun _discr_ -> (match (_discr_) with
| Sig_declare_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 270 "FStar.Syntax.Syntax.fst"
let is_Sig_let = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

# 274 "FStar.Syntax.Syntax.fst"
let is_Sig_main = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

# 276 "FStar.Syntax.Syntax.fst"
let is_Sig_assume = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

# 280 "FStar.Syntax.Syntax.fst"
let is_Sig_new_effect = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 281 "FStar.Syntax.Syntax.fst"
let is_Sig_sub_effect = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 282 "FStar.Syntax.Syntax.fst"
let is_Sig_effect_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 283 "FStar.Syntax.Syntax.fst"
let is_Sig_pragma = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 240 "FStar.Syntax.Syntax.fst"
let ___Sig_inductive_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_29_231) -> begin
_29_231
end))

# 253 "FStar.Syntax.Syntax.fst"
let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_29_234) -> begin
_29_234
end))

# 257 "FStar.Syntax.Syntax.fst"
let ___Sig_datacon____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_29_237) -> begin
_29_237
end))

# 265 "FStar.Syntax.Syntax.fst"
let ___Sig_declare_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_29_240) -> begin
_29_240
end))

# 270 "FStar.Syntax.Syntax.fst"
let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_29_243) -> begin
_29_243
end))

# 274 "FStar.Syntax.Syntax.fst"
let ___Sig_main____0 : sigelt  ->  (term * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_29_246) -> begin
_29_246
end))

# 276 "FStar.Syntax.Syntax.fst"
let ___Sig_assume____0 : sigelt  ->  (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_29_249) -> begin
_29_249
end))

# 280 "FStar.Syntax.Syntax.fst"
let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_29_252) -> begin
_29_252
end))

# 281 "FStar.Syntax.Syntax.fst"
let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_29_255) -> begin
_29_255
end))

# 282 "FStar.Syntax.Syntax.fst"
let ___Sig_effect_abbrev____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_29_258) -> begin
_29_258
end))

# 283 "FStar.Syntax.Syntax.fst"
let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_29_261) -> begin
_29_261
end))

# 284 "FStar.Syntax.Syntax.fst"
type sigelts =
sigelt Prims.list

# 286 "FStar.Syntax.Syntax.fst"
type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}

# 286 "FStar.Syntax.Syntax.fst"
let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

# 292 "FStar.Syntax.Syntax.fst"
type path =
Prims.string Prims.list

# 293 "FStar.Syntax.Syntax.fst"
type subst_t =
subst_elt Prims.list

# 294 "FStar.Syntax.Syntax.fst"
type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax

# 295 "FStar.Syntax.Syntax.fst"
type mk_t =
(term', term') mk_t_a

# 358 "FStar.Syntax.Syntax.fst"
let withinfo = (fun v s r -> {v = v; ty = s; p = r})

# 359 "FStar.Syntax.Syntax.fst"
let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))

# 361 "FStar.Syntax.Syntax.fst"
let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))

# 362 "FStar.Syntax.Syntax.fst"
let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (
# 363 "FStar.Syntax.Syntax.fst"
let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = 0) then begin
(x.index - y.index)
end else begin
i
end))

# 368 "FStar.Syntax.Syntax.fst"
let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(FStar_Ident.range_of_lid l)
end))

# 371 "FStar.Syntax.Syntax.fst"
let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)

# 372 "FStar.Syntax.Syntax.fst"
let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (
# 372 "FStar.Syntax.Syntax.fst"
let _29_293 = x
in {ppname = (FStar_Ident.mk_ident (x.ppname.FStar_Ident.idText, r)); index = _29_293.index; sort = _29_293.sort}))

# 379 "FStar.Syntax.Syntax.fst"
let syn = (fun p k f -> (f k p))

# 380 "FStar.Syntax.Syntax.fst"
let mk_fvs = (fun _29_298 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 381 "FStar.Syntax.Syntax.fst"
let mk_uvs = (fun _29_299 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 382 "FStar.Syntax.Syntax.fst"
let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun _29_300 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))

# 383 "FStar.Syntax.Syntax.fst"
let new_uv_set : Prims.unit  ->  uvars = (fun _29_302 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _29_310 _29_314 -> (match ((_29_310, _29_314)) with
| ((x, _29_309), (y, _29_313)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _29_306 -> (match (_29_306) with
| (x, _29_305) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 385 "FStar.Syntax.Syntax.fst"
let new_universe_uvar_set : Prims.unit  ->  universe_uvar FStar_Util.set = (fun _29_315 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))

# 388 "FStar.Syntax.Syntax.fst"
let no_names : freenames = (new_bv_set ())

# 389 "FStar.Syntax.Syntax.fst"
let no_uvs : uvars = (new_uv_set ())

# 390 "FStar.Syntax.Syntax.fst"
let no_universe_uvars : universe_uvar FStar_Util.set = (new_universe_uvar_set ())

# 391 "FStar.Syntax.Syntax.fst"
let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars}

# 396 "FStar.Syntax.Syntax.fst"
let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 397 "FStar.Syntax.Syntax.fst"
let memo_no_names : freenames Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))

# 398 "FStar.Syntax.Syntax.fst"
let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))

# 399 "FStar.Syntax.Syntax.fst"
let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))

# 402 "FStar.Syntax.Syntax.fst"
let mk = (fun t topt r -> (let _110_1166 = (FStar_Util.mk_ref topt)
in (let _110_1165 = (FStar_Util.mk_ref None)
in {n = t; tk = _110_1166; pos = r; vars = _110_1165})))

# 408 "FStar.Syntax.Syntax.fst"
let bv_to_tm : bv  ->  term = (fun bv -> (let _110_1169 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (Some (bv.sort.n)) _110_1169)))

# 409 "FStar.Syntax.Syntax.fst"
let bv_to_name : bv  ->  term = (fun bv -> (let _110_1172 = (range_of_bv bv)
in (mk (Tm_name (bv)) (Some (bv.sort.n)) _110_1172)))

# 410 "FStar.Syntax.Syntax.fst"
let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _29_334 -> begin
(mk (Tm_app ((t1, args))) k p)
end))

# 414 "FStar.Syntax.Syntax.fst"
let mk_Tm_uinst : term  ->  universes  ->  term = (fun t _29_1 -> (match (_29_1) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_29_340) -> begin
(mk (Tm_uinst ((t, us))) None t.pos)
end
| _29_343 -> begin
(FStar_All.failwith "Unexpected universe instantiation")
end)
end))

# 421 "FStar.Syntax.Syntax.fst"
let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _29_353 -> begin
(mk_Tm_app t args' kopt r)
end))

# 424 "FStar.Syntax.Syntax.fst"
let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))

# 425 "FStar.Syntax.Syntax.fst"
let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  term = (fun lr pos -> (let _110_1207 = (let _110_1206 = (let _110_1205 = (FStar_Util.mk_ref None)
in (lr, _110_1205))
in Tm_delayed (_110_1206))
in (mk _110_1207 None pos)))

# 426 "FStar.Syntax.Syntax.fst"
let mk_Total : typ  ->  comp = (fun t -> (mk (Total (t)) None t.pos))

# 427 "FStar.Syntax.Syntax.fst"
let mk_GTotal : typ  ->  comp = (fun t -> (mk (GTotal (t)) None t.pos))

# 428 "FStar.Syntax.Syntax.fst"
let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))

# 429 "FStar.Syntax.Syntax.fst"
let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun _29_368 -> (match (_29_368) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 430 "FStar.Syntax.Syntax.fst"
let mk_subst : subst_t  ->  subst_t = (fun s -> s)

# 431 "FStar.Syntax.Syntax.fst"
let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_elt Prims.list = (fun x s -> (x)::s)

# 432 "FStar.Syntax.Syntax.fst"
let argpos : arg  ->  FStar_Range.range = (fun x -> (Prims.fst x).pos)

# 434 "FStar.Syntax.Syntax.fst"
let tun : (term', term') syntax = (mk Tm_unknown None FStar_Range.dummyRange)

# 435 "FStar.Syntax.Syntax.fst"
let teff : (term', term') syntax = (mk (Tm_constant (FStar_Const.Const_effect)) (Some (Tm_unknown)) FStar_Range.dummyRange)

# 436 "FStar.Syntax.Syntax.fst"
let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| _29_377 -> begin
false
end))

# 439 "FStar.Syntax.Syntax.fst"
let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (_29_380) -> begin
true
end
| _29_383 -> begin
false
end))

# 442 "FStar.Syntax.Syntax.fst"
let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident ("_", FStar_Range.dummyRange))

# 443 "FStar.Syntax.Syntax.fst"
let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = 0; sort = k})

# 444 "FStar.Syntax.Syntax.fst"
let mk_binder : bv  ->  binder = (fun a -> (a, None))

# 445 "FStar.Syntax.Syntax.fst"
let null_binder : term  ->  binder = (fun t -> (let _110_1234 = (null_bv t)
in (_110_1234, None)))

# 446 "FStar.Syntax.Syntax.fst"
let imp_tag : arg_qualifier = Implicit (false)

# 447 "FStar.Syntax.Syntax.fst"
let iarg : term  ->  arg = (fun t -> (t, Some (imp_tag)))

# 448 "FStar.Syntax.Syntax.fst"
let as_arg : term  ->  arg = (fun t -> (t, None))

# 449 "FStar.Syntax.Syntax.fst"
let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 450 "FStar.Syntax.Syntax.fst"
let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))

# 452 "FStar.Syntax.Syntax.fst"
let is_top_level : letbinding Prims.list  ->  Prims.bool = (fun _29_2 -> (match (_29_2) with
| {lbname = FStar_Util.Inr (_29_403); lbunivs = _29_401; lbtyp = _29_399; lbeff = _29_397; lbdef = _29_395}::_29_393 -> begin
true
end
| _29_408 -> begin
false
end))

# 456 "FStar.Syntax.Syntax.fst"
let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun _29_413 out -> (match (_29_413) with
| (x, _29_412) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))

# 459 "FStar.Syntax.Syntax.fst"
let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 460 "FStar.Syntax.Syntax.fst"
let binders_of_freenames : freenames  ->  binders = (fun fvs -> (let _110_1254 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _110_1254 binders_of_list)))

# 461 "FStar.Syntax.Syntax.fst"
let is_implicit : aqual  ->  Prims.bool = (fun _29_3 -> (match (_29_3) with
| Some (Implicit (_29_420)) -> begin
true
end
| _29_424 -> begin
false
end))

# 462 "FStar.Syntax.Syntax.fst"
let as_implicit : Prims.bool  ->  aqual = (fun _29_4 -> (match (_29_4) with
| true -> begin
Some (imp_tag)
end
| _29_428 -> begin
None
end))

# 464 "FStar.Syntax.Syntax.fst"
let pat_bvs : pat  ->  bv Prims.list = (fun p -> (
# 465 "FStar.Syntax.Syntax.fst"
let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (_29_443, pats) -> begin
(FStar_List.fold_left (fun b _29_451 -> (match (_29_451) with
| (p, _29_450) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj (p::_29_453) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let _110_1267 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev _110_1267))))

# 476 "FStar.Syntax.Syntax.fst"
let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (
# 477 "FStar.Syntax.Syntax.fst"
let x = (FStar_ST.alloc 0)
in (
# 478 "FStar.Syntax.Syntax.fst"
let gen = (fun _29_461 -> (match (()) with
| () -> begin
(
# 478 "FStar.Syntax.Syntax.fst"
let _29_462 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (
# 479 "FStar.Syntax.Syntax.fst"
let reset = (fun _29_465 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x 0)
end))
in (gen, reset))))

# 481 "FStar.Syntax.Syntax.fst"
let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)

# 482 "FStar.Syntax.Syntax.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)

# 483 "FStar.Syntax.Syntax.fst"
let freshen_bv : bv  ->  bv = (fun bv -> (
# 483 "FStar.Syntax.Syntax.fst"
let _29_467 = bv
in (let _110_1286 = (next_id ())
in {ppname = _29_467.ppname; index = _110_1286; sort = _29_467.sort})))

# 484 "FStar.Syntax.Syntax.fst"
let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun _29_5 -> (match (_29_5) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))

# 487 "FStar.Syntax.Syntax.fst"
let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (
# 488 "FStar.Syntax.Syntax.fst"
let id = (FStar_Ident.mk_ident (s, (range_of_ropt r)))
in (let _110_1295 = (next_id ())
in {ppname = id; index = _110_1295; sort = t})))

# 490 "FStar.Syntax.Syntax.fst"
let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv "x" ropt t))

# 491 "FStar.Syntax.Syntax.fst"
let new_univ_name : FStar_Range.range Prims.option  ->  univ_name = (fun ropt -> (
# 492 "FStar.Syntax.Syntax.fst"
let id = (next_id ())
in (let _110_1303 = (let _110_1302 = (FStar_Util.string_of_int id)
in (_110_1302, (range_of_ropt ropt)))
in (FStar_Ident.mk_ident _110_1303))))

# 494 "FStar.Syntax.Syntax.fst"
let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})

# 495 "FStar.Syntax.Syntax.fst"
let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _29_497 -> begin
false
end))

# 499 "FStar.Syntax.Syntax.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun _29_501 _29_505 -> (match ((_29_501, _29_505)) with
| ((fv1, _29_500), (fv2, _29_504)) -> begin
(FStar_Ident.lid_equals fv1.v fv2.v)
end))

# 500 "FStar.Syntax.Syntax.fst"
let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (
# 500 "FStar.Syntax.Syntax.fst"
let _29_508 = bv
in {ppname = (FStar_Ident.mk_ident (bv.ppname.FStar_Ident.idText, r)); index = _29_508.index; sort = _29_508.sort}))

# 501 "FStar.Syntax.Syntax.fst"
let lid_as_fv : FStar_Ident.lident  ->  fv_qual Prims.option  ->  fv = (fun l dc -> (let _110_1326 = (withinfo l tun (FStar_Ident.range_of_lid l))
in (_110_1326, dc)))

# 502 "FStar.Syntax.Syntax.fst"
let fv_to_tm : fv  ->  term = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid (Prims.fst fv).v)))

# 503 "FStar.Syntax.Syntax.fst"
let fvar : fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  term = (fun dc l r -> (let _110_1337 = (let _110_1336 = (let _110_1335 = (FStar_Ident.set_lid_range l r)
in (lid_as_fv _110_1335 dc))
in Tm_fvar (_110_1336))
in (mk _110_1337 None r)))




