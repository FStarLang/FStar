
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
| Err (_30_6) -> begin
_30_6
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
| Error (_30_8) -> begin
_30_8
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
| Warning (_30_10) -> begin
_30_10
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
| SetOptions (_30_20) -> begin
_30_20
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
| Implicit (_30_24) -> begin
_30_24
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
| U_succ (_30_27) -> begin
_30_27
end))

# 58 "FStar.Syntax.Syntax.fst"
let ___U_max____0 : universe  ->  universe Prims.list = (fun projectee -> (match (projectee) with
| U_max (_30_30) -> begin
_30_30
end))

# 59 "FStar.Syntax.Syntax.fst"
let ___U_bvar____0 : universe  ->  Prims.int = (fun projectee -> (match (projectee) with
| U_bvar (_30_33) -> begin
_30_33
end))

# 60 "FStar.Syntax.Syntax.fst"
let ___U_name____0 : universe  ->  univ_name = (fun projectee -> (match (projectee) with
| U_name (_30_36) -> begin
_30_36
end))

# 61 "FStar.Syntax.Syntax.fst"
let ___U_unif____0 : universe  ->  universe Prims.option FStar_Unionfind.uvar = (fun projectee -> (match (projectee) with
| U_unif (_30_39) -> begin
_30_39
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
| DB of (Prims.int * term)
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
| Tm_bvar (_30_68) -> begin
_30_68
end))

# 71 "FStar.Syntax.Syntax.fst"
let ___Tm_name____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_name (_30_71) -> begin
_30_71
end))

# 72 "FStar.Syntax.Syntax.fst"
let ___Tm_fvar____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| Tm_fvar (_30_74) -> begin
_30_74
end))

# 73 "FStar.Syntax.Syntax.fst"
let ___Tm_uinst____0 : term'  ->  (term * universes) = (fun projectee -> (match (projectee) with
| Tm_uinst (_30_77) -> begin
_30_77
end))

# 74 "FStar.Syntax.Syntax.fst"
let ___Tm_constant____0 : term'  ->  sconst = (fun projectee -> (match (projectee) with
| Tm_constant (_30_80) -> begin
_30_80
end))

# 75 "FStar.Syntax.Syntax.fst"
let ___Tm_type____0 : term'  ->  universe = (fun projectee -> (match (projectee) with
| Tm_type (_30_83) -> begin
_30_83
end))

# 76 "FStar.Syntax.Syntax.fst"
let ___Tm_abs____0 : term'  ->  (binders * term * lcomp Prims.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_30_86) -> begin
_30_86
end))

# 77 "FStar.Syntax.Syntax.fst"
let ___Tm_arrow____0 : term'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Tm_arrow (_30_89) -> begin
_30_89
end))

# 78 "FStar.Syntax.Syntax.fst"
let ___Tm_refine____0 : term'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Tm_refine (_30_92) -> begin
_30_92
end))

# 79 "FStar.Syntax.Syntax.fst"
let ___Tm_app____0 : term'  ->  (term * args) = (fun projectee -> (match (projectee) with
| Tm_app (_30_95) -> begin
_30_95
end))

# 80 "FStar.Syntax.Syntax.fst"
let ___Tm_match____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_30_98) -> begin
_30_98
end))

# 81 "FStar.Syntax.Syntax.fst"
let ___Tm_ascribed____0 : term'  ->  (term * term * FStar_Ident.lident Prims.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_30_101) -> begin
_30_101
end))

# 82 "FStar.Syntax.Syntax.fst"
let ___Tm_let____0 : term'  ->  (letbindings * term) = (fun projectee -> (match (projectee) with
| Tm_let (_30_104) -> begin
_30_104
end))

# 83 "FStar.Syntax.Syntax.fst"
let ___Tm_uvar____0 : term'  ->  (uvar * term) = (fun projectee -> (match (projectee) with
| Tm_uvar (_30_107) -> begin
_30_107
end))

# 84 "FStar.Syntax.Syntax.fst"
let ___Tm_delayed____0 : term'  ->  (((term * subst_ts), Prims.unit  ->  term) FStar_Util.either * term memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_30_110) -> begin
_30_110
end))

# 86 "FStar.Syntax.Syntax.fst"
let ___Tm_meta____0 : term'  ->  (term * metadata) = (fun projectee -> (match (projectee) with
| Tm_meta (_30_113) -> begin
_30_113
end))

# 90 "FStar.Syntax.Syntax.fst"
let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_30_116) -> begin
_30_116
end))

# 91 "FStar.Syntax.Syntax.fst"
let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_30_119) -> begin
_30_119
end))

# 92 "FStar.Syntax.Syntax.fst"
let ___Pat_cons____0 : pat'  ->  (fv * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_30_122) -> begin
_30_122
end))

# 93 "FStar.Syntax.Syntax.fst"
let ___Pat_var____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_var (_30_125) -> begin
_30_125
end))

# 94 "FStar.Syntax.Syntax.fst"
let ___Pat_wild____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_wild (_30_128) -> begin
_30_128
end))

# 95 "FStar.Syntax.Syntax.fst"
let ___Pat_dot_term____0 : pat'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_30_131) -> begin
_30_131
end))

# 110 "FStar.Syntax.Syntax.fst"
let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_30_136) -> begin
_30_136
end))

# 111 "FStar.Syntax.Syntax.fst"
let ___GTotal____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| GTotal (_30_139) -> begin
_30_139
end))

# 112 "FStar.Syntax.Syntax.fst"
let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_30_142) -> begin
_30_142
end))

# 128 "FStar.Syntax.Syntax.fst"
let ___DECREASES____0 : cflags  ->  term = (fun projectee -> (match (projectee) with
| DECREASES (_30_145) -> begin
_30_145
end))

# 131 "FStar.Syntax.Syntax.fst"
let ___Meta_pattern____0 : metadata  ->  args Prims.list = (fun projectee -> (match (projectee) with
| Meta_pattern (_30_148) -> begin
_30_148
end))

# 132 "FStar.Syntax.Syntax.fst"
let ___Meta_named____0 : metadata  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Meta_named (_30_151) -> begin
_30_151
end))

# 133 "FStar.Syntax.Syntax.fst"
let ___Meta_labeled____0 : metadata  ->  (Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_30_154) -> begin
_30_154
end))

# 134 "FStar.Syntax.Syntax.fst"
let ___Meta_desugared____0 : metadata  ->  meta_source_info = (fun projectee -> (match (projectee) with
| Meta_desugared (_30_157) -> begin
_30_157
end))

# 137 "FStar.Syntax.Syntax.fst"
let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_30_160) -> begin
_30_160
end))

# 146 "FStar.Syntax.Syntax.fst"
let ___Record_projector____0 : fv_qual  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Record_projector (_30_163) -> begin
_30_163
end))

# 147 "FStar.Syntax.Syntax.fst"
let ___Record_ctor____0 : fv_qual  ->  (FStar_Ident.lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_30_166) -> begin
_30_166
end))

# 152 "FStar.Syntax.Syntax.fst"
let ___DB____0 : subst_elt  ->  (Prims.int * term) = (fun projectee -> (match (projectee) with
| DB (_30_169) -> begin
_30_169
end))

# 153 "FStar.Syntax.Syntax.fst"
let ___NM____0 : subst_elt  ->  (bv * Prims.int) = (fun projectee -> (match (projectee) with
| NM (_30_172) -> begin
_30_172
end))

# 154 "FStar.Syntax.Syntax.fst"
let ___NT____0 : subst_elt  ->  (bv * term) = (fun projectee -> (match (projectee) with
| NT (_30_175) -> begin
_30_175
end))

# 155 "FStar.Syntax.Syntax.fst"
let ___UN____0 : subst_elt  ->  (Prims.int * universe) = (fun projectee -> (match (projectee) with
| UN (_30_178) -> begin
_30_178
end))

# 156 "FStar.Syntax.Syntax.fst"
let ___UD____0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_30_181) -> begin
_30_181
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
| DefaultEffect (_30_188) -> begin
_30_188
end))

# 200 "FStar.Syntax.Syntax.fst"
let ___Discriminator____0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Discriminator (_30_191) -> begin
_30_191
end))

# 201 "FStar.Syntax.Syntax.fst"
let ___Projector____0 : qualifier  ->  (FStar_Ident.lident * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_30_194) -> begin
_30_194
end))

# 202 "FStar.Syntax.Syntax.fst"
let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_30_197) -> begin
_30_197
end))

# 203 "FStar.Syntax.Syntax.fst"
let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_30_200) -> begin
_30_200
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
| Sig_inductive_typ (_30_230) -> begin
_30_230
end))

# 253 "FStar.Syntax.Syntax.fst"
let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_30_233) -> begin
_30_233
end))

# 257 "FStar.Syntax.Syntax.fst"
let ___Sig_datacon____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_30_236) -> begin
_30_236
end))

# 265 "FStar.Syntax.Syntax.fst"
let ___Sig_declare_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_30_239) -> begin
_30_239
end))

# 270 "FStar.Syntax.Syntax.fst"
let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_30_242) -> begin
_30_242
end))

# 274 "FStar.Syntax.Syntax.fst"
let ___Sig_main____0 : sigelt  ->  (term * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_30_245) -> begin
_30_245
end))

# 276 "FStar.Syntax.Syntax.fst"
let ___Sig_assume____0 : sigelt  ->  (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_30_248) -> begin
_30_248
end))

# 280 "FStar.Syntax.Syntax.fst"
let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_30_251) -> begin
_30_251
end))

# 281 "FStar.Syntax.Syntax.fst"
let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_30_254) -> begin
_30_254
end))

# 282 "FStar.Syntax.Syntax.fst"
let ___Sig_effect_abbrev____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_30_257) -> begin
_30_257
end))

# 283 "FStar.Syntax.Syntax.fst"
let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_30_260) -> begin
_30_260
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

# 357 "FStar.Syntax.Syntax.fst"
let withinfo = (fun v s r -> {v = v; ty = s; p = r})

# 358 "FStar.Syntax.Syntax.fst"
let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))

# 360 "FStar.Syntax.Syntax.fst"
let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))

# 361 "FStar.Syntax.Syntax.fst"
let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (
# 362 "FStar.Syntax.Syntax.fst"
let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = 0) then begin
(x.index - y.index)
end else begin
i
end))

# 367 "FStar.Syntax.Syntax.fst"
let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(FStar_Ident.range_of_lid l)
end))

# 370 "FStar.Syntax.Syntax.fst"
let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)

# 371 "FStar.Syntax.Syntax.fst"
let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (
# 371 "FStar.Syntax.Syntax.fst"
let _30_292 = x
in {ppname = (FStar_Ident.mk_ident (x.ppname.FStar_Ident.idText, r)); index = _30_292.index; sort = _30_292.sort}))

# 378 "FStar.Syntax.Syntax.fst"
let syn = (fun p k f -> (f k p))

# 379 "FStar.Syntax.Syntax.fst"
let mk_fvs = (fun _30_297 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 380 "FStar.Syntax.Syntax.fst"
let mk_uvs = (fun _30_298 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 381 "FStar.Syntax.Syntax.fst"
let new_bv_set : Prims.unit  ->  bv FStar_Util.set = (fun _30_299 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))

# 382 "FStar.Syntax.Syntax.fst"
let new_uv_set : Prims.unit  ->  uvars = (fun _30_301 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _30_309 _30_313 -> (match ((_30_309, _30_313)) with
| ((x, _30_308), (y, _30_312)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _30_305 -> (match (_30_305) with
| (x, _30_304) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 384 "FStar.Syntax.Syntax.fst"
let new_universe_uvar_set : Prims.unit  ->  universe_uvar FStar_Util.set = (fun _30_314 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))

# 387 "FStar.Syntax.Syntax.fst"
let no_names : freenames = (new_bv_set ())

# 388 "FStar.Syntax.Syntax.fst"
let no_uvs : uvars = (new_uv_set ())

# 389 "FStar.Syntax.Syntax.fst"
let no_universe_uvars : universe_uvar FStar_Util.set = (new_universe_uvar_set ())

# 390 "FStar.Syntax.Syntax.fst"
let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars}

# 395 "FStar.Syntax.Syntax.fst"
let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 396 "FStar.Syntax.Syntax.fst"
let memo_no_names : freenames Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))

# 397 "FStar.Syntax.Syntax.fst"
let freenames_of_list : bv Prims.list  ->  freenames = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))

# 398 "FStar.Syntax.Syntax.fst"
let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))

# 401 "FStar.Syntax.Syntax.fst"
let mk = (fun t topt r -> (let _109_1166 = (FStar_Util.mk_ref topt)
in (let _109_1165 = (FStar_Util.mk_ref None)
in {n = t; tk = _109_1166; pos = r; vars = _109_1165})))

# 407 "FStar.Syntax.Syntax.fst"
let bv_to_tm : bv  ->  term = (fun bv -> (let _109_1169 = (range_of_bv bv)
in (mk (Tm_bvar (bv)) (Some (bv.sort.n)) _109_1169)))

# 408 "FStar.Syntax.Syntax.fst"
let bv_to_name : bv  ->  term = (fun bv -> (let _109_1172 = (range_of_bv bv)
in (mk (Tm_name (bv)) (Some (bv.sort.n)) _109_1172)))

# 409 "FStar.Syntax.Syntax.fst"
let mk_Tm_app : term  ->  args  ->  mk_t = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _30_333 -> begin
(mk (Tm_app ((t1, args))) k p)
end))

# 413 "FStar.Syntax.Syntax.fst"
let mk_Tm_uinst : term  ->  universes  ->  term = (fun t _30_1 -> (match (_30_1) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_30_339) -> begin
(mk (Tm_uinst ((t, us))) None t.pos)
end
| _30_342 -> begin
(FStar_All.failwith "Unexpected universe instantiation")
end)
end))

# 420 "FStar.Syntax.Syntax.fst"
let extend_app_n : term  ->  args  ->  mk_t = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _30_352 -> begin
(mk_Tm_app t args' kopt r)
end))

# 423 "FStar.Syntax.Syntax.fst"
let extend_app : term  ->  arg  ->  mk_t = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))

# 424 "FStar.Syntax.Syntax.fst"
let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  term = (fun lr pos -> (let _109_1207 = (let _109_1206 = (let _109_1205 = (FStar_Util.mk_ref None)
in (lr, _109_1205))
in Tm_delayed (_109_1206))
in (mk _109_1207 None pos)))

# 425 "FStar.Syntax.Syntax.fst"
let mk_Total : typ  ->  comp = (fun t -> (mk (Total (t)) None t.pos))

# 426 "FStar.Syntax.Syntax.fst"
let mk_GTotal : typ  ->  comp = (fun t -> (mk (GTotal (t)) None t.pos))

# 427 "FStar.Syntax.Syntax.fst"
let mk_Comp : comp_typ  ->  comp = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))

# 428 "FStar.Syntax.Syntax.fst"
let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun _30_367 -> (match (_30_367) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 429 "FStar.Syntax.Syntax.fst"
let mk_subst : subst_t  ->  subst_t = (fun s -> s)

# 430 "FStar.Syntax.Syntax.fst"
let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_elt Prims.list = (fun x s -> (x)::s)

# 431 "FStar.Syntax.Syntax.fst"
let argpos : arg  ->  FStar_Range.range = (fun x -> (Prims.fst x).pos)

# 433 "FStar.Syntax.Syntax.fst"
let tun : (term', term') syntax = (mk Tm_unknown None FStar_Range.dummyRange)

# 434 "FStar.Syntax.Syntax.fst"
let teff : (term', term') syntax = (mk (Tm_constant (FStar_Const.Const_effect)) (Some (Tm_unknown)) FStar_Range.dummyRange)

# 435 "FStar.Syntax.Syntax.fst"
let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| _30_376 -> begin
false
end))

# 438 "FStar.Syntax.Syntax.fst"
let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (_30_379) -> begin
true
end
| _30_382 -> begin
false
end))

# 441 "FStar.Syntax.Syntax.fst"
let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident ("_", FStar_Range.dummyRange))

# 442 "FStar.Syntax.Syntax.fst"
let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = 0; sort = k})

# 443 "FStar.Syntax.Syntax.fst"
let mk_binder : bv  ->  binder = (fun a -> (a, None))

# 444 "FStar.Syntax.Syntax.fst"
let null_binder : term  ->  binder = (fun t -> (let _109_1234 = (null_bv t)
in (_109_1234, None)))

# 445 "FStar.Syntax.Syntax.fst"
let imp_tag : arg_qualifier = Implicit (false)

# 446 "FStar.Syntax.Syntax.fst"
let iarg : term  ->  arg = (fun t -> (t, Some (imp_tag)))

# 447 "FStar.Syntax.Syntax.fst"
let as_arg : term  ->  arg = (fun t -> (t, None))

# 448 "FStar.Syntax.Syntax.fst"
let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 449 "FStar.Syntax.Syntax.fst"
let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))

# 451 "FStar.Syntax.Syntax.fst"
let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun _30_394 out -> (match (_30_394) with
| (x, _30_393) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))

# 454 "FStar.Syntax.Syntax.fst"
let binders_of_list : bv Prims.list  ->  binders = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 455 "FStar.Syntax.Syntax.fst"
let binders_of_freenames : freenames  ->  binders = (fun fvs -> (let _109_1252 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _109_1252 binders_of_list)))

# 456 "FStar.Syntax.Syntax.fst"
let is_implicit : aqual  ->  Prims.bool = (fun _30_2 -> (match (_30_2) with
| Some (Implicit (_30_401)) -> begin
true
end
| _30_405 -> begin
false
end))

# 457 "FStar.Syntax.Syntax.fst"
let as_implicit : Prims.bool  ->  aqual = (fun _30_3 -> (match (_30_3) with
| true -> begin
Some (imp_tag)
end
| _30_409 -> begin
None
end))

# 459 "FStar.Syntax.Syntax.fst"
let pat_bvs : pat  ->  bv Prims.list = (fun p -> (
# 460 "FStar.Syntax.Syntax.fst"
let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (_30_424, pats) -> begin
(FStar_List.fold_left (fun b _30_432 -> (match (_30_432) with
| (p, _30_431) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj (p::_30_434) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let _109_1265 = (aux [] p)
in (FStar_All.pipe_left FStar_List.rev _109_1265))))

# 471 "FStar.Syntax.Syntax.fst"
let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (
# 472 "FStar.Syntax.Syntax.fst"
let x = (FStar_ST.alloc 0)
in (
# 473 "FStar.Syntax.Syntax.fst"
let gen = (fun _30_442 -> (match (()) with
| () -> begin
(
# 473 "FStar.Syntax.Syntax.fst"
let _30_443 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (
# 474 "FStar.Syntax.Syntax.fst"
let reset = (fun _30_446 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x 0)
end))
in (gen, reset))))

# 476 "FStar.Syntax.Syntax.fst"
let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)

# 477 "FStar.Syntax.Syntax.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)

# 478 "FStar.Syntax.Syntax.fst"
let freshen_bv : bv  ->  bv = (fun bv -> (
# 478 "FStar.Syntax.Syntax.fst"
let _30_448 = bv
in (let _109_1285 = (next_id ())
in {ppname = _30_448.ppname; index = _109_1285; sort = _30_448.sort})))

# 479 "FStar.Syntax.Syntax.fst"
let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun _30_4 -> (match (_30_4) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))

# 482 "FStar.Syntax.Syntax.fst"
let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (
# 483 "FStar.Syntax.Syntax.fst"
let id = (FStar_Ident.mk_ident (s, (range_of_ropt r)))
in (let _109_1294 = (next_id ())
in {ppname = id; index = _109_1294; sort = t})))

# 485 "FStar.Syntax.Syntax.fst"
let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv "x" ropt t))

# 486 "FStar.Syntax.Syntax.fst"
let new_univ_name : FStar_Range.range Prims.option  ->  univ_name = (fun ropt -> (
# 487 "FStar.Syntax.Syntax.fst"
let id = (next_id ())
in (let _109_1302 = (let _109_1301 = (FStar_Util.string_of_int id)
in (_109_1301, (range_of_ropt ropt)))
in (FStar_Ident.mk_ident _109_1302))))

# 489 "FStar.Syntax.Syntax.fst"
let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})

# 490 "FStar.Syntax.Syntax.fst"
let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _30_478 -> begin
false
end))

# 494 "FStar.Syntax.Syntax.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun _30_482 _30_486 -> (match ((_30_482, _30_486)) with
| ((fv1, _30_481), (fv2, _30_485)) -> begin
(FStar_Ident.lid_equals fv1.v fv2.v)
end))

# 495 "FStar.Syntax.Syntax.fst"
let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (
# 495 "FStar.Syntax.Syntax.fst"
let _30_489 = bv
in {ppname = (FStar_Ident.mk_ident (bv.ppname.FStar_Ident.idText, r)); index = _30_489.index; sort = _30_489.sort}))

# 496 "FStar.Syntax.Syntax.fst"
let lid_as_fv : FStar_Ident.lident  ->  fv_qual Prims.option  ->  fv = (fun l dc -> (let _109_1325 = (withinfo l tun (FStar_Ident.range_of_lid l))
in (_109_1325, dc)))

# 497 "FStar.Syntax.Syntax.fst"
let fv_to_tm : fv  ->  term = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid (Prims.fst fv).v)))

# 498 "FStar.Syntax.Syntax.fst"
let fvar : fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  term = (fun dc l r -> (let _109_1336 = (let _109_1335 = (let _109_1334 = (FStar_Ident.set_lid_range l r)
in (lid_as_fv _109_1334 dc))
in Tm_fvar (_109_1335))
in (mk _109_1336 None r)))




