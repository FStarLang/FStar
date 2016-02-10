
open Prims
# 28 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

exception Err of (Prims.string)

# 28 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Err____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (_32_6) -> begin
_32_6
end))

# 29 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

exception Error of ((Prims.string * FStar_Range.range))

# 29 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Error____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (_32_8) -> begin
_32_8
end))

# 30 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

exception Warning of ((Prims.string * FStar_Range.range))

# 30 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Warning____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (_32_10) -> begin
_32_10
end))

# 33 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type ('a, 't) withinfo_t =
{v : 'a; ty : 't; p : FStar_Range.range}

# 33 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkwithinfo_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkwithinfo_t"))))

# 40 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type 't var =
(FStar_Ident.lident, 't) withinfo_t

# 41 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type fieldname =
FStar_Ident.lident

# 43 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type sconst =
FStar_Const.sconst

# 45 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type pragma =
| SetOptions of Prims.string
| ResetOptions

# 46 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_32_20) -> begin
_32_20
end))

# 49 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type 'a memo =
'a Prims.option FStar_ST.ref

# 51 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type arg_qualifier =
| Implicit
| Equality

# 52 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type aqual =
arg_qualifier Prims.option

# 55 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

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

# 56 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_zero = (fun _discr_ -> (match (_discr_) with
| U_zero (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_succ = (fun _discr_ -> (match (_discr_) with
| U_succ (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_max = (fun _discr_ -> (match (_discr_) with
| U_max (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_bvar = (fun _discr_ -> (match (_discr_) with
| U_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_name = (fun _discr_ -> (match (_discr_) with
| U_name (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_unif = (fun _discr_ -> (match (_discr_) with
| U_unif (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_U_unknown = (fun _discr_ -> (match (_discr_) with
| U_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___U_succ____0 : universe  ->  universe = (fun projectee -> (match (projectee) with
| U_succ (_32_24) -> begin
_32_24
end))

# 58 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___U_max____0 : universe  ->  universe Prims.list = (fun projectee -> (match (projectee) with
| U_max (_32_27) -> begin
_32_27
end))

# 59 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___U_bvar____0 : universe  ->  Prims.int = (fun projectee -> (match (projectee) with
| U_bvar (_32_30) -> begin
_32_30
end))

# 60 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___U_name____0 : universe  ->  univ_name = (fun projectee -> (match (projectee) with
| U_name (_32_33) -> begin
_32_33
end))

# 61 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___U_unif____0 : universe  ->  universe Prims.option FStar_Unionfind.uvar = (fun projectee -> (match (projectee) with
| U_unif (_32_36) -> begin
_32_36
end))

# 65 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type universe_uvar =
universe Prims.option FStar_Unionfind.uvar

# 66 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type univ_names =
univ_name Prims.list

# 67 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type universes =
universe Prims.list

# 69 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

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

# 70 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_bvar = (fun _discr_ -> (match (_discr_) with
| Tm_bvar (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_name = (fun _discr_ -> (match (_discr_) with
| Tm_name (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_fvar = (fun _discr_ -> (match (_discr_) with
| Tm_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_uinst = (fun _discr_ -> (match (_discr_) with
| Tm_uinst (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_constant = (fun _discr_ -> (match (_discr_) with
| Tm_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_type = (fun _discr_ -> (match (_discr_) with
| Tm_type (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_abs = (fun _discr_ -> (match (_discr_) with
| Tm_abs (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_arrow = (fun _discr_ -> (match (_discr_) with
| Tm_arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_refine = (fun _discr_ -> (match (_discr_) with
| Tm_refine (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_app = (fun _discr_ -> (match (_discr_) with
| Tm_app (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_match = (fun _discr_ -> (match (_discr_) with
| Tm_match (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_ascribed = (fun _discr_ -> (match (_discr_) with
| Tm_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_let = (fun _discr_ -> (match (_discr_) with
| Tm_let (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_uvar = (fun _discr_ -> (match (_discr_) with
| Tm_uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_delayed = (fun _discr_ -> (match (_discr_) with
| Tm_delayed (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_meta = (fun _discr_ -> (match (_discr_) with
| Tm_meta (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Tm_unknown = (fun _discr_ -> (match (_discr_) with
| Tm_unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Pat_constant = (fun _discr_ -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Pat_disj = (fun _discr_ -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Pat_cons = (fun _discr_ -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Pat_var = (fun _discr_ -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Pat_wild = (fun _discr_ -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Pat_dot_term = (fun _discr_ -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

# 96 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkletbinding : letbinding  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkletbinding"))))

# 103 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkcomp_typ : comp_typ  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcomp_typ"))))

# 110 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Total = (fun _discr_ -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_GTotal = (fun _discr_ -> (match (_discr_) with
| GTotal (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Comp = (fun _discr_ -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_TOTAL = (fun _discr_ -> (match (_discr_) with
| TOTAL (_) -> begin
true
end
| _ -> begin
false
end))

# 123 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_MLEFFECT = (fun _discr_ -> (match (_discr_) with
| MLEFFECT (_) -> begin
true
end
| _ -> begin
false
end))

# 124 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_RETURN = (fun _discr_ -> (match (_discr_) with
| RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 125 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_PARTIAL_RETURN = (fun _discr_ -> (match (_discr_) with
| PARTIAL_RETURN (_) -> begin
true
end
| _ -> begin
false
end))

# 126 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_SOMETRIVIAL = (fun _discr_ -> (match (_discr_) with
| SOMETRIVIAL (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_LEMMA = (fun _discr_ -> (match (_discr_) with
| LEMMA (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_DECREASES = (fun _discr_ -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

# 131 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Meta_pattern = (fun _discr_ -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Meta_named = (fun _discr_ -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Meta_labeled = (fun _discr_ -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Meta_desugared = (fun _discr_ -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Uvar = (fun _ _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
true
end
| _ -> begin
false
end))

# 137 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Fixed = (fun _ _discr_ -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

# 139 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Data_app = (fun _discr_ -> (match (_discr_) with
| Data_app (_) -> begin
true
end
| _ -> begin
false
end))

# 140 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sequence = (fun _discr_ -> (match (_discr_) with
| Sequence (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Primop = (fun _discr_ -> (match (_discr_) with
| Primop (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Masked_effect = (fun _discr_ -> (match (_discr_) with
| Masked_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Meta_smt_pat = (fun _discr_ -> (match (_discr_) with
| Meta_smt_pat (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Data_ctor = (fun _discr_ -> (match (_discr_) with
| Data_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Record_projector = (fun _discr_ -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Record_ctor = (fun _discr_ -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

# 152 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_DB = (fun _discr_ -> (match (_discr_) with
| DB (_) -> begin
true
end
| _ -> begin
false
end))

# 153 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_NM = (fun _discr_ -> (match (_discr_) with
| NM (_) -> begin
true
end
| _ -> begin
false
end))

# 154 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_NT = (fun _discr_ -> (match (_discr_) with
| NT (_) -> begin
true
end
| _ -> begin
false
end))

# 155 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_UN = (fun _discr_ -> (match (_discr_) with
| UN (_) -> begin
true
end
| _ -> begin
false
end))

# 156 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_UD = (fun _discr_ -> (match (_discr_) with
| UD (_) -> begin
true
end
| _ -> begin
false
end))

# 159 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mksyntax = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksyntax"))))

# 165 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkbv : bv  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbv"))))

# 171 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkfree_vars : free_vars  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfree_vars"))))

# 176 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mklcomp : lcomp  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklcomp"))))

# 70 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_bvar____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_bvar (_32_65) -> begin
_32_65
end))

# 71 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_name____0 : term'  ->  bv = (fun projectee -> (match (projectee) with
| Tm_name (_32_68) -> begin
_32_68
end))

# 72 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_fvar____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| Tm_fvar (_32_71) -> begin
_32_71
end))

# 73 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_uinst____0 : term'  ->  (term * universes) = (fun projectee -> (match (projectee) with
| Tm_uinst (_32_74) -> begin
_32_74
end))

# 74 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_constant____0 : term'  ->  sconst = (fun projectee -> (match (projectee) with
| Tm_constant (_32_77) -> begin
_32_77
end))

# 75 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_type____0 : term'  ->  universe = (fun projectee -> (match (projectee) with
| Tm_type (_32_80) -> begin
_32_80
end))

# 76 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_abs____0 : term'  ->  (binders * term * lcomp Prims.option) = (fun projectee -> (match (projectee) with
| Tm_abs (_32_83) -> begin
_32_83
end))

# 77 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_arrow____0 : term'  ->  (binders * comp) = (fun projectee -> (match (projectee) with
| Tm_arrow (_32_86) -> begin
_32_86
end))

# 78 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_refine____0 : term'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Tm_refine (_32_89) -> begin
_32_89
end))

# 79 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_app____0 : term'  ->  (term * args) = (fun projectee -> (match (projectee) with
| Tm_app (_32_92) -> begin
_32_92
end))

# 80 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_match____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Tm_match (_32_95) -> begin
_32_95
end))

# 81 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_ascribed____0 : term'  ->  (term * term * FStar_Ident.lident Prims.option) = (fun projectee -> (match (projectee) with
| Tm_ascribed (_32_98) -> begin
_32_98
end))

# 82 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_let____0 : term'  ->  (letbindings * term) = (fun projectee -> (match (projectee) with
| Tm_let (_32_101) -> begin
_32_101
end))

# 83 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_uvar____0 : term'  ->  (uvar * term) = (fun projectee -> (match (projectee) with
| Tm_uvar (_32_104) -> begin
_32_104
end))

# 84 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_delayed____0 : term'  ->  (((term * subst_ts), Prims.unit  ->  term) FStar_Util.either * term memo) = (fun projectee -> (match (projectee) with
| Tm_delayed (_32_107) -> begin
_32_107
end))

# 86 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Tm_meta____0 : term'  ->  (term * metadata) = (fun projectee -> (match (projectee) with
| Tm_meta (_32_110) -> begin
_32_110
end))

# 90 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Pat_constant____0 : pat'  ->  sconst = (fun projectee -> (match (projectee) with
| Pat_constant (_32_113) -> begin
_32_113
end))

# 91 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Pat_disj____0 : pat'  ->  pat Prims.list = (fun projectee -> (match (projectee) with
| Pat_disj (_32_116) -> begin
_32_116
end))

# 92 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Pat_cons____0 : pat'  ->  (fv * (pat * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| Pat_cons (_32_119) -> begin
_32_119
end))

# 93 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Pat_var____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_var (_32_122) -> begin
_32_122
end))

# 94 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Pat_wild____0 : pat'  ->  bv = (fun projectee -> (match (projectee) with
| Pat_wild (_32_125) -> begin
_32_125
end))

# 95 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Pat_dot_term____0 : pat'  ->  (bv * term) = (fun projectee -> (match (projectee) with
| Pat_dot_term (_32_128) -> begin
_32_128
end))

# 110 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Total____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| Total (_32_133) -> begin
_32_133
end))

# 111 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___GTotal____0 : comp'  ->  typ = (fun projectee -> (match (projectee) with
| GTotal (_32_136) -> begin
_32_136
end))

# 112 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Comp____0 : comp'  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_32_139) -> begin
_32_139
end))

# 128 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___DECREASES____0 : cflags  ->  term = (fun projectee -> (match (projectee) with
| DECREASES (_32_142) -> begin
_32_142
end))

# 131 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Meta_pattern____0 : metadata  ->  args Prims.list = (fun projectee -> (match (projectee) with
| Meta_pattern (_32_145) -> begin
_32_145
end))

# 132 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Meta_named____0 : metadata  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Meta_named (_32_148) -> begin
_32_148
end))

# 133 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Meta_labeled____0 : metadata  ->  (Prims.string * FStar_Range.range * Prims.bool) = (fun projectee -> (match (projectee) with
| Meta_labeled (_32_151) -> begin
_32_151
end))

# 134 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Meta_desugared____0 : metadata  ->  meta_source_info = (fun projectee -> (match (projectee) with
| Meta_desugared (_32_154) -> begin
_32_154
end))

# 137 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Fixed____0 = (fun projectee -> (match (projectee) with
| Fixed (_32_157) -> begin
_32_157
end))

# 146 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Record_projector____0 : fv_qual  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Record_projector (_32_160) -> begin
_32_160
end))

# 147 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Record_ctor____0 : fv_qual  ->  (FStar_Ident.lident * fieldname Prims.list) = (fun projectee -> (match (projectee) with
| Record_ctor (_32_163) -> begin
_32_163
end))

# 152 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___DB____0 : subst_elt  ->  (Prims.int * term) = (fun projectee -> (match (projectee) with
| DB (_32_166) -> begin
_32_166
end))

# 153 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___NM____0 : subst_elt  ->  (bv * Prims.int) = (fun projectee -> (match (projectee) with
| NM (_32_169) -> begin
_32_169
end))

# 154 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___NT____0 : subst_elt  ->  (bv * term) = (fun projectee -> (match (projectee) with
| NT (_32_172) -> begin
_32_172
end))

# 155 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___UN____0 : subst_elt  ->  (Prims.int * universe) = (fun projectee -> (match (projectee) with
| UN (_32_175) -> begin
_32_175
end))

# 156 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___UD____0 : subst_elt  ->  (univ_name * Prims.int) = (fun projectee -> (match (projectee) with
| UD (_32_178) -> begin
_32_178
end))

# 183 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type tscheme =
(univ_name Prims.list * typ)

# 185 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type freenames_l =
bv Prims.list

# 186 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type formula =
typ

# 187 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type formulae =
typ Prims.list

# 188 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

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

# 189 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 190 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 191 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 192 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))

# 193 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable (_) -> begin
true
end
| _ -> begin
false
end))

# 194 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))

# 195 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 196 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 197 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 199 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 200 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Discriminator = (fun _discr_ -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

# 201 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

# 202 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_RecordType = (fun _discr_ -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

# 203 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_RecordConstructor = (fun _discr_ -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 204 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_ExceptionConstructor = (fun _discr_ -> (match (_discr_) with
| ExceptionConstructor (_) -> begin
true
end
| _ -> begin
false
end))

# 205 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_HasMaskedEffect = (fun _discr_ -> (match (_discr_) with
| HasMaskedEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 206 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 196 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___DefaultEffect____0 : qualifier  ->  FStar_Ident.lident Prims.option = (fun projectee -> (match (projectee) with
| DefaultEffect (_32_185) -> begin
_32_185
end))

# 200 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Discriminator____0 : qualifier  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| Discriminator (_32_188) -> begin
_32_188
end))

# 201 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Projector____0 : qualifier  ->  (FStar_Ident.lident * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_32_191) -> begin
_32_191
end))

# 202 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___RecordType____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordType (_32_194) -> begin
_32_194
end))

# 203 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___RecordConstructor____0 : qualifier  ->  fieldname Prims.list = (fun projectee -> (match (projectee) with
| RecordConstructor (_32_197) -> begin
_32_197
end))

# 208 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type tycon =
(FStar_Ident.lident * binders * typ)

# 209 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type monad_abbrev =
{mabbrev : FStar_Ident.lident; parms : binders; def : typ}

# 209 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkmonad_abbrev : monad_abbrev  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmonad_abbrev"))))

# 214 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type sub_eff =
{source : FStar_Ident.lident; target : FStar_Ident.lident; lift : tscheme}

# 214 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mksub_eff : sub_eff  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksub_eff"))))

# 219 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

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

# 219 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkeff_decl : eff_decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeff_decl"))))

# 240 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_inductive_typ = (fun _discr_ -> (match (_discr_) with
| Sig_inductive_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 253 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_bundle = (fun _discr_ -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

# 257 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_datacon = (fun _discr_ -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

# 265 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_declare_typ = (fun _discr_ -> (match (_discr_) with
| Sig_declare_typ (_) -> begin
true
end
| _ -> begin
false
end))

# 270 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_let = (fun _discr_ -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

# 274 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_main = (fun _discr_ -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

# 276 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_assume = (fun _discr_ -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

# 280 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_new_effect = (fun _discr_ -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 281 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_sub_effect = (fun _discr_ -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 282 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_effect_abbrev = (fun _discr_ -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 283 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Sig_pragma = (fun _discr_ -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 240 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_inductive_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * typ * FStar_Ident.lident Prims.list * FStar_Ident.lident Prims.list * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_inductive_typ (_32_227) -> begin
_32_227
end))

# 253 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_bundle____0 : sigelt  ->  (sigelt Prims.list * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_bundle (_32_230) -> begin
_32_230
end))

# 257 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_datacon____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * FStar_Ident.lident * Prims.int * qualifier Prims.list * FStar_Ident.lident Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_datacon (_32_233) -> begin
_32_233
end))

# 265 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_declare_typ____0 : sigelt  ->  (FStar_Ident.lident * univ_names * typ * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_declare_typ (_32_236) -> begin
_32_236
end))

# 270 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_let____0 : sigelt  ->  (letbindings * FStar_Range.range * FStar_Ident.lident Prims.list * qualifier Prims.list) = (fun projectee -> (match (projectee) with
| Sig_let (_32_239) -> begin
_32_239
end))

# 274 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_main____0 : sigelt  ->  (term * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_main (_32_242) -> begin
_32_242
end))

# 276 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_assume____0 : sigelt  ->  (FStar_Ident.lident * formula * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_assume (_32_245) -> begin
_32_245
end))

# 280 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_new_effect____0 : sigelt  ->  (eff_decl * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_new_effect (_32_248) -> begin
_32_248
end))

# 281 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_sub_effect____0 : sigelt  ->  (sub_eff * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_sub_effect (_32_251) -> begin
_32_251
end))

# 282 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_effect_abbrev____0 : sigelt  ->  (FStar_Ident.lident * univ_names * binders * comp * qualifier Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_effect_abbrev (_32_254) -> begin
_32_254
end))

# 283 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let ___Sig_pragma____0 : sigelt  ->  (pragma * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Sig_pragma (_32_257) -> begin
_32_257
end))

# 284 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type sigelts =
sigelt Prims.list

# 286 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type modul =
{name : FStar_Ident.lident; declarations : sigelts; exports : sigelts; is_interface : Prims.bool}

# 286 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_Mkmodul : modul  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkmodul"))))

# 292 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type path =
Prims.string Prims.list

# 293 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type subst_t =
subst_elt Prims.list

# 294 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type ('a, 'b) mk_t_a =
'b Prims.option  ->  FStar_Range.range  ->  ('a, 'b) syntax

# 295 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

type mk_t =
(term', term') mk_t_a

# 300 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let withinfo = (fun v s r -> {v = v; ty = s; p = r})

# 301 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let withsort = (fun v s -> (withinfo v s FStar_Range.dummyRange))

# 303 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let bv_eq : bv  ->  bv  ->  Prims.bool = (fun bv1 bv2 -> ((bv1.ppname.FStar_Ident.idText = bv2.ppname.FStar_Ident.idText) && (bv1.index = bv2.index)))

# 304 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let order_bv : bv  ->  bv  ->  Prims.int = (fun x y -> (let i = (FStar_String.compare x.ppname.FStar_Ident.idText y.ppname.FStar_Ident.idText)
in if (i = 0) then begin
(x.index - y.index)
end else begin
i
end))

# 310 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let range_of_lbname : lbname  ->  FStar_Range.range = (fun l -> (match (l) with
| FStar_Util.Inl (x) -> begin
x.ppname.FStar_Ident.idRange
end
| FStar_Util.Inr (l) -> begin
(FStar_Ident.range_of_lid l)
end))

# 313 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let range_of_bv : bv  ->  FStar_Range.range = (fun x -> x.ppname.FStar_Ident.idRange)

# 314 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let set_range_of_bv : bv  ->  FStar_Range.range  ->  bv = (fun x r -> (let _32_283 = x
in {ppname = (FStar_Ident.mk_ident (x.ppname.FStar_Ident.idText, r)); index = _32_283.index; sort = _32_283.sort}))

# 321 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let syn = (fun p k f -> (f k p))

# 322 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_fvs = (fun _32_288 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 323 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_uvs = (fun _32_289 -> (match (()) with
| () -> begin
(FStar_Util.mk_ref None)
end))

# 324 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let new_bv_set : Prims.unit  ->  (bv Prims.list * (bv  ->  bv  ->  Prims.bool)) = (fun _32_290 -> (match (()) with
| () -> begin
(FStar_Util.new_set order_bv (fun x -> (x.index + (FStar_Util.hashcode x.ppname.FStar_Ident.idText))))
end))

# 325 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let new_uv_set : Prims.unit  ->  uvars = (fun _32_292 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun _32_300 _32_304 -> (match ((_32_300, _32_304)) with
| ((x, _32_299), (y, _32_303)) -> begin
((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))
end)) (fun _32_296 -> (match (_32_296) with
| (x, _32_295) -> begin
(FStar_Unionfind.uvar_id x)
end)))
end))

# 327 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let new_universe_uvar_set : Prims.unit  ->  (universe_uvar Prims.list * (universe_uvar  ->  universe_uvar  ->  Prims.bool)) = (fun _32_305 -> (match (()) with
| () -> begin
(FStar_Util.new_set (fun x y -> ((FStar_Unionfind.uvar_id x) - (FStar_Unionfind.uvar_id y))) (fun x -> (FStar_Unionfind.uvar_id x)))
end))

# 330 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let no_names : (bv Prims.list * (bv  ->  bv  ->  Prims.bool)) = (new_bv_set ())

# 331 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let no_uvs : uvars = (new_uv_set ())

# 332 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let no_universe_uvars : (universe_uvar Prims.list * (universe_uvar  ->  universe_uvar  ->  Prims.bool)) = (new_universe_uvar_set ())

# 333 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let empty_free_vars : free_vars = {free_names = no_names; free_uvars = no_uvs; free_univs = no_universe_uvars}

# 338 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let memo_no_uvs : uvars Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_uvs)))

# 339 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let memo_no_names : (bv Prims.list * (bv  ->  bv  ->  Prims.bool)) Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (no_names)))

# 340 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let freenames_of_list : bv Prims.list  ->  (bv Prims.list * (bv  ->  bv  ->  Prims.bool)) = (fun l -> (FStar_List.fold_right FStar_Util.set_add l no_names))

# 341 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let list_of_freenames : freenames  ->  bv Prims.list = (fun fvs -> (FStar_Util.set_elements fvs))

# 344 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk = (fun t topt r -> (let _134_1198 = (FStar_Util.mk_ref topt)
in (let _134_1197 = (FStar_Util.mk_ref None)
in {n = t; tk = _134_1198; pos = r; vars = _134_1197})))

# 350 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let bv_to_tm : bv  ->  (term', term') syntax = (fun bv -> (mk (Tm_bvar (bv)) (Some (bv.sort.n)) (range_of_bv bv)))

# 351 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let bv_to_name : bv  ->  (term', term') syntax = (fun bv -> (mk (Tm_name (bv)) (Some (bv.sort.n)) (range_of_bv bv)))

# 352 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_Tm_app : typ  ->  arg Prims.list  ->  term' Prims.option  ->  Prims.int64  ->  (term', term') syntax = (fun t1 args k p -> (match (args) with
| [] -> begin
t1
end
| _32_324 -> begin
(mk (Tm_app ((t1, args))) k p)
end))

# 356 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_Tm_uinst : term  ->  universe Prims.list  ->  term = (fun t _32_1 -> (match (_32_1) with
| [] -> begin
t
end
| us -> begin
(match (t.n) with
| Tm_fvar (_32_330) -> begin
(mk (Tm_uinst ((t, us))) None t.pos)
end
| _32_333 -> begin
(FStar_All.failwith "Unexpected universe instantiation")
end)
end))

# 363 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let extend_app_n : (term', term') syntax  ->  ((term', term') syntax * arg_qualifier Prims.option) Prims.list  ->  term' Prims.option  ->  Prims.int64  ->  (term', term') syntax = (fun t args' kopt r -> (match (t.n) with
| Tm_app (head, args) -> begin
(mk_Tm_app head (FStar_List.append args args') kopt r)
end
| _32_343 -> begin
(mk_Tm_app t args' kopt r)
end))

# 366 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let extend_app : (term', term') syntax  ->  ((term', term') syntax * arg_qualifier Prims.option)  ->  term' Prims.option  ->  Prims.int64  ->  (term', term') syntax = (fun t arg kopt r -> (extend_app_n t ((arg)::[]) kopt r))

# 367 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_Tm_delayed : ((term * subst_ts), Prims.unit  ->  term) FStar_Util.either  ->  FStar_Range.range  ->  (term', term') syntax = (fun lr pos -> (let _134_1253 = (let _134_1252 = (let _134_1251 = (FStar_Util.mk_ref None)
in (lr, _134_1251))
in Tm_delayed (_134_1252))
in (mk _134_1253 None pos)))

# 368 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_Total : typ  ->  (comp', Prims.unit) syntax = (fun t -> (mk (Total (t)) None t.pos))

# 369 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_GTotal : typ  ->  (comp', Prims.unit) syntax = (fun t -> (mk (GTotal (t)) None t.pos))

# 370 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_Comp : comp_typ  ->  (comp', Prims.unit) syntax = (fun ct -> (mk (Comp (ct)) None ct.result_typ.pos))

# 371 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_lb : (lbname * univ_name Prims.list * FStar_Ident.lident * typ * term)  ->  letbinding = (fun _32_358 -> (match (_32_358) with
| (x, univs, eff, t, e) -> begin
{lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e}
end))

# 372 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_subst : subst_t  ->  subst_t = (fun s -> s)

# 373 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let extend_subst : subst_elt  ->  subst_elt Prims.list  ->  subst_elt Prims.list = (fun x s -> (x)::s)

# 374 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let argpos : arg  ->  FStar_Range.range = (fun x -> (Prims.fst x).pos)

# 376 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let tun : (term', term') syntax = (mk Tm_unknown None FStar_Range.dummyRange)

# 377 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let teff : (term', term') syntax = (mk (Tm_constant (FStar_Const.Const_effect)) (Some (Tm_unknown)) FStar_Range.dummyRange)

# 378 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_teff : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_constant (FStar_Const.Const_effect) -> begin
true
end
| _32_367 -> begin
false
end))

# 381 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_type : term  ->  Prims.bool = (fun t -> (match (t.n) with
| Tm_type (_32_370) -> begin
true
end
| _32_373 -> begin
false
end))

# 384 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let null_id : FStar_Ident.ident = (FStar_Ident.mk_ident ("_", FStar_Range.dummyRange))

# 385 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let null_bv : term  ->  bv = (fun k -> {ppname = null_id; index = 0; sort = k})

# 386 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mk_binder : bv  ->  (bv * arg_qualifier Prims.option) = (fun a -> (a, None))

# 387 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let null_binder : term  ->  (bv * arg_qualifier Prims.option) = (fun t -> ((null_bv t), None))

# 388 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let iarg : (term', term') syntax  ->  ((term', term') syntax * arg_qualifier Prims.option) = (fun t -> (t, Some (Implicit)))

# 389 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let as_arg : (term', term') syntax  ->  ((term', term') syntax * arg_qualifier Prims.option) = (fun t -> (t, None))

# 390 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_null_bv : bv  ->  Prims.bool = (fun b -> (b.ppname.FStar_Ident.idText = null_id.FStar_Ident.idText))

# 391 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_null_binder : binder  ->  Prims.bool = (fun b -> (is_null_bv (Prims.fst b)))

# 393 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let freenames_of_binders : binders  ->  freenames = (fun bs -> (FStar_List.fold_right (fun _32_385 out -> (match (_32_385) with
| (x, _32_384) -> begin
(FStar_Util.set_add x out)
end)) bs no_names))

# 396 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let binders_of_list : bv Prims.list  ->  (bv * arg_qualifier Prims.option) Prims.list = (fun fvs -> (FStar_All.pipe_right fvs (FStar_List.map (fun t -> (t, None)))))

# 397 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let binders_of_freenames : freenames  ->  (bv * arg_qualifier Prims.option) Prims.list = (fun fvs -> (let _134_1297 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _134_1297 binders_of_list)))

# 398 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let is_implicit : arg_qualifier Prims.option  ->  Prims.bool = (fun _32_2 -> (match (_32_2) with
| Some (Implicit) -> begin
true
end
| _32_394 -> begin
false
end))

# 399 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let as_implicit : Prims.bool  ->  arg_qualifier Prims.option = (fun _32_3 -> (match (_32_3) with
| true -> begin
Some (Implicit)
end
| _32_398 -> begin
None
end))

# 401 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let pat_bvs : pat  ->  bv Prims.list = (fun p -> (let rec aux = (fun b p -> (match (p.v) with
| (Pat_dot_term (_)) | (Pat_constant (_)) -> begin
b
end
| (Pat_wild (x)) | (Pat_var (x)) -> begin
(x)::b
end
| Pat_cons (_32_413, pats) -> begin
(FStar_List.fold_left (fun b _32_421 -> (match (_32_421) with
| (p, _32_420) -> begin
(aux b p)
end)) b pats)
end
| Pat_disj (p::_32_423) -> begin
(aux b p)
end
| Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (aux [] p)))

# 413 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let gen_reset : ((Prims.unit  ->  Prims.int) * (Prims.unit  ->  Prims.unit)) = (let x = (FStar_ST.alloc 0)
in (let gen = (fun _32_431 -> (match (()) with
| () -> begin
(let _32_432 = (FStar_Util.incr x)
in (FStar_ST.read x))
end))
in (let reset = (fun _32_435 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals x 0)
end))
in (gen, reset))))

# 418 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let next_id : Prims.unit  ->  Prims.int = (Prims.fst gen_reset)

# 419 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let reset_gensym : Prims.unit  ->  Prims.unit = (Prims.snd gen_reset)

# 420 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let freshen_bv : bv  ->  bv = (fun bv -> (let _32_437 = bv
in (let _134_1328 = (next_id ())
in {ppname = _32_437.ppname; index = _134_1328; sort = _32_437.sort})))

# 421 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let range_of_ropt : FStar_Range.range Prims.option  ->  FStar_Range.range = (fun _32_4 -> (match (_32_4) with
| None -> begin
FStar_Range.dummyRange
end
| Some (r) -> begin
r
end))

# 424 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let gen_bv : Prims.string  ->  FStar_Range.range Prims.option  ->  typ  ->  bv = (fun s r t -> (let id = (FStar_Ident.mk_ident (s, (range_of_ropt r)))
in (let _134_1337 = (next_id ())
in {ppname = id; index = _134_1337; sort = t})))

# 427 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let new_bv : FStar_Range.range Prims.option  ->  typ  ->  bv = (fun ropt t -> (gen_bv "x" ropt t))

# 428 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let new_univ_name : FStar_Range.range Prims.option  ->  FStar_Ident.ident = (fun ropt -> (let id = (next_id ())
in (let _134_1345 = (let _134_1344 = (FStar_Util.string_of_int id)
in (_134_1344, (range_of_ropt ropt)))
in (FStar_Ident.mk_ident _134_1345))))

# 431 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let mkbv : FStar_Ident.ident  ->  Prims.int  ->  term  ->  bv = (fun x y t -> {ppname = x; index = y; sort = t})

# 432 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let lbname_eq : (bv, FStar_Ident.lident) FStar_Util.either  ->  (bv, FStar_Ident.lident) FStar_Util.either  ->  Prims.bool = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bv_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _32_467 -> begin
false
end))

# 436 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let fv_eq : fv  ->  fv  ->  Prims.bool = (fun _32_471 _32_475 -> (match ((_32_471, _32_475)) with
| ((fv1, _32_470), (fv2, _32_474)) -> begin
(FStar_Ident.lid_equals fv1.v fv2.v)
end))

# 437 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let set_bv_range : bv  ->  FStar_Range.range  ->  bv = (fun bv r -> (let _32_478 = bv
in {ppname = (FStar_Ident.mk_ident (bv.ppname.FStar_Ident.idText, r)); index = _32_478.index; sort = _32_478.sort}))

# 438 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let lid_as_fv : FStar_Ident.lid  ->  fv_qual Prims.option  ->  ((FStar_Ident.lid, (term', term') syntax) withinfo_t * fv_qual Prims.option) = (fun l dc -> ((withinfo l tun (FStar_Ident.range_of_lid l)), dc))

# 439 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let fv_to_tm : fv  ->  (term', term') syntax = (fun fv -> (mk (Tm_fvar (fv)) None (FStar_Ident.range_of_lid (Prims.fst fv).v)))

# 440 "D:\\workspace\\FStar\\src\\syntax\\syntax.fs"

let fvar : fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  (term', term') syntax = (fun dc l r -> (let _134_1378 = (let _134_1377 = (let _134_1376 = (FStar_Ident.set_lid_range l r)
in (lid_as_fv _134_1376 dc))
in Tm_fvar (_134_1377))
in (mk _134_1378 None r)))




