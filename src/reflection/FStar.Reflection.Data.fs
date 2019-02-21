#light "off"
module FStar.Reflection.Data
open FStar.String
open FStar.Syntax.Syntax
module Ident = FStar.Ident
module Range = FStar.Range
module Z     = FStar.BigInt

type name = list<string>
type typ  = term
type binders = list<binder>

type vconst =
    | C_Unit
    | C_Int of Z.t
    | C_True
    | C_False
    | C_String of string
    | C_Range of Range.range
    | C_Reify
    | C_Reflect of name

type pattern =
    | Pat_Constant of vconst
    | Pat_Cons     of fv * list<pattern>
    | Pat_Var      of bv
    | Pat_Wild     of bv
    | Pat_Dot_Term of bv * term

type branch = pattern * term

type aqualv =
    | Q_Implicit
    | Q_Explicit
    | Q_Meta of term

type argv = term * aqualv

type term_view =
    | Tv_Var    of bv
    | Tv_BVar   of bv
    | Tv_FVar   of fv
    | Tv_App    of term * argv
    | Tv_Abs    of binder * term
    | Tv_Arrow  of binder * comp
    | Tv_Type   of unit
    | Tv_Refine of bv * term
    | Tv_Const  of vconst
    | Tv_Uvar   of Z.t * ctx_uvar_and_subst
    | Tv_Let    of bool * bv * term * term
    | Tv_Match  of term * list<branch>
    | Tv_AscribedT of term * term * option<term>
    | Tv_AscribedC of term * comp * option<term>
    | Tv_Unknown

type bv_view = {
    bv_ppname : string;
    bv_index : Z.t;
    bv_sort : typ;
}

type binder_view = bv * aqualv

type comp_view =
    | C_Total of typ * option<term> //optional decreases clause
    | C_Lemma of term * term
    | C_Unknown

type sigelt_view =
    | Sg_Let of bool * fv * list<univ_name> * typ * term
    | Sg_Inductive of name * list<univ_name> * list<binder> * typ * list<name> // name, params, type, constructors
    | Sg_Constructor of name * typ
    | Unk

type var = Z.t

type exp =
    | Unit
    | Var of var
    | Mult of exp * exp

(* Contains all lids and terms needed for embedding/unembedding *)

type refl_constant = {
    lid : FStar.Ident.lid;
    fv : fv;
    t : term;
}

let refl_constant_lid rc = rc.lid
let refl_constant_term rc = rc.t
let fstar_refl_lid s = Ident.lid_of_path (["FStar"; "Reflection"]@s) Range.dummyRange

let fstar_refl_basic_lid  s = fstar_refl_lid ["Basic";  s]
let fstar_refl_syntax_lid s = fstar_refl_lid ["Syntax"; s]
let fstar_refl_types_lid  s = fstar_refl_lid ["Types";  s]
let fstar_refl_data_lid   s = fstar_refl_lid ["Data";   s]

let fstar_refl_data_const s =
    let lid = fstar_refl_data_lid s in
    { lid = lid
    ; fv  = lid_as_fv lid delta_constant (Some Data_ctor)
    ; t   = tdataconstr lid
    }

let mk_refl_types_lid_as_term  (s:string) = tconst  (fstar_refl_types_lid s)
let mk_refl_types_lid_as_fv    (s:string) = fvconst (fstar_refl_types_lid s)
let mk_refl_syntax_lid_as_term (s:string) = tconst  (fstar_refl_syntax_lid s)
let mk_refl_syntax_lid_as_fv   (s:string) = fvconst (fstar_refl_syntax_lid s)
let mk_refl_data_lid_as_term   (s:string) = tconst  (fstar_refl_data_lid s)
let mk_refl_data_lid_as_fv     (s:string) = fvconst (fstar_refl_data_lid s)

let mk_inspect_pack_pair s =
    let inspect_lid = fstar_refl_basic_lid ("inspect" ^ s) in
    let pack_lid    = fstar_refl_basic_lid ("pack" ^ s) in
    let inspect_fv  = lid_as_fv inspect_lid (Delta_constant_at_level 1) None in
    let pack_fv     = lid_as_fv pack_lid    (Delta_constant_at_level 1) None in
    let inspect     = { lid = inspect_lid ; fv = inspect_fv ; t = fv_to_tm inspect_fv } in
    let pack        = { lid = pack_lid    ; fv = pack_fv    ; t = fv_to_tm pack_fv } in
    (inspect, pack)

let fstar_refl_inspect_ln     , fstar_refl_pack_ln     = mk_inspect_pack_pair "_ln"
let fstar_refl_inspect_fv     , fstar_refl_pack_fv     = mk_inspect_pack_pair "_fv"
let fstar_refl_inspect_bv     , fstar_refl_pack_bv     = mk_inspect_pack_pair "_bv"
let fstar_refl_inspect_binder , fstar_refl_pack_binder = mk_inspect_pack_pair "_binder"
let fstar_refl_inspect_comp   , fstar_refl_pack_comp   = mk_inspect_pack_pair "_comp"
let fstar_refl_inspect_sigelt , fstar_refl_pack_sigelt = mk_inspect_pack_pair "_sigelt"

(* assumed types *)
let fstar_refl_env              = mk_refl_types_lid_as_term "env"
let fstar_refl_env_fv           = mk_refl_types_lid_as_fv   "env"
let fstar_refl_bv               = mk_refl_types_lid_as_term "bv"
let fstar_refl_bv_fv            = mk_refl_types_lid_as_fv   "bv"
let fstar_refl_fv               = mk_refl_types_lid_as_term "fv"
let fstar_refl_fv_fv            = mk_refl_types_lid_as_fv   "fv"
let fstar_refl_comp             = mk_refl_types_lid_as_term "comp"
let fstar_refl_comp_fv          = mk_refl_types_lid_as_fv   "comp"
let fstar_refl_binder           = mk_refl_types_lid_as_term "binder"
let fstar_refl_binder_fv        = mk_refl_types_lid_as_fv   "binder"
let fstar_refl_sigelt           = mk_refl_types_lid_as_term "sigelt"
let fstar_refl_sigelt_fv        = mk_refl_types_lid_as_fv   "sigelt"
let fstar_refl_term             = mk_refl_types_lid_as_term "term"
let fstar_refl_term_fv          = mk_refl_types_lid_as_fv   "term"
let fstar_refl_ident            = mk_refl_types_lid_as_term "ident"
let fstar_refl_ident_fv         = mk_refl_types_lid_as_fv   "ident"
let fstar_refl_univ_name        = mk_refl_types_lid_as_term "univ_name"
let fstar_refl_univ_name_fv     = mk_refl_types_lid_as_fv   "univ_name"

(* auxiliary types *)
let fstar_refl_aqualv           = mk_refl_data_lid_as_term "aqualv"
let fstar_refl_aqualv_fv        = mk_refl_data_lid_as_fv "aqualv"
let fstar_refl_comp_view        = mk_refl_data_lid_as_term "comp_view"
let fstar_refl_comp_view_fv     = mk_refl_data_lid_as_fv "comp_view"
let fstar_refl_term_view        = mk_refl_data_lid_as_term "term_view"
let fstar_refl_term_view_fv     = mk_refl_data_lid_as_fv "term_view"
let fstar_refl_pattern          = mk_refl_data_lid_as_term "pattern"
let fstar_refl_pattern_fv       = mk_refl_data_lid_as_fv "pattern"
let fstar_refl_branch           = mk_refl_data_lid_as_term "branch"
let fstar_refl_branch_fv        = mk_refl_data_lid_as_fv "branch"
let fstar_refl_bv_view          = mk_refl_data_lid_as_term "bv_view"
let fstar_refl_bv_view_fv       = mk_refl_data_lid_as_fv "bv_view"
let fstar_refl_vconst           = mk_refl_data_lid_as_term "vconst"
let fstar_refl_vconst_fv        = mk_refl_data_lid_as_fv "vconst"
let fstar_refl_sigelt_view      = mk_refl_data_lid_as_term "sigelt_view"
let fstar_refl_sigelt_view_fv   = mk_refl_data_lid_as_fv "sigelt_view"
let fstar_refl_exp              = mk_refl_data_lid_as_term "exp"
let fstar_refl_exp_fv           = mk_refl_data_lid_as_fv "exp"

(* bv_view, this is a record constructor *)

let ref_Mk_bv =
    let lid = fstar_refl_data_lid "Mkbv_view" in
    let attr = Record_ctor (fstar_refl_data_lid "bv_view", [
                                Ident.mk_ident ("bv_ppname", Range.dummyRange);
                                Ident.mk_ident ("bv_index" , Range.dummyRange);
                                Ident.mk_ident ("bv_sort"  , Range.dummyRange)]) in
    let fv = lid_as_fv lid delta_constant (Some attr) in
    { lid = lid
    ; fv  = fv
    ; t   = fv_to_tm fv
    }

(* quals *)
let ref_Q_Explicit = fstar_refl_data_const "Q_Explicit"
let ref_Q_Implicit = fstar_refl_data_const "Q_Implicit"
let ref_Q_Meta     = fstar_refl_data_const "Q_Meta"

(* const *)
let ref_C_Unit      = fstar_refl_data_const "C_Unit"
let ref_C_True      = fstar_refl_data_const "C_True"
let ref_C_False     = fstar_refl_data_const "C_False"
let ref_C_Int       = fstar_refl_data_const "C_Int"
let ref_C_String    = fstar_refl_data_const "C_String"
let ref_C_Range     = fstar_refl_data_const "C_Range"
let ref_C_Reify     = fstar_refl_data_const "C_Reify"
let ref_C_Reflect   = fstar_refl_data_const "C_Reflect"

(* pattern *)
let ref_Pat_Constant = fstar_refl_data_const "Pat_Constant"
let ref_Pat_Cons     = fstar_refl_data_const "Pat_Cons"
let ref_Pat_Var      = fstar_refl_data_const "Pat_Var"
let ref_Pat_Wild     = fstar_refl_data_const "Pat_Wild"
let ref_Pat_Dot_Term = fstar_refl_data_const "Pat_Dot_Term"

(* term_view *)
let ref_Tv_Var     = fstar_refl_data_const "Tv_Var"
let ref_Tv_BVar    = fstar_refl_data_const "Tv_BVar"
let ref_Tv_FVar    = fstar_refl_data_const "Tv_FVar"
let ref_Tv_App     = fstar_refl_data_const "Tv_App"
let ref_Tv_Abs     = fstar_refl_data_const "Tv_Abs"
let ref_Tv_Arrow   = fstar_refl_data_const "Tv_Arrow"
let ref_Tv_Type    = fstar_refl_data_const "Tv_Type"
let ref_Tv_Refine  = fstar_refl_data_const "Tv_Refine"
let ref_Tv_Const   = fstar_refl_data_const "Tv_Const"
let ref_Tv_Uvar    = fstar_refl_data_const "Tv_Uvar"
let ref_Tv_Let     = fstar_refl_data_const "Tv_Let"
let ref_Tv_Match   = fstar_refl_data_const "Tv_Match"
let ref_Tv_AscT    = fstar_refl_data_const "Tv_AscribedT"
let ref_Tv_AscC    = fstar_refl_data_const "Tv_AscribedC"
let ref_Tv_Unknown = fstar_refl_data_const "Tv_Unknown"

(* comp_view *)
let ref_C_Total   = fstar_refl_data_const "C_Total"
let ref_C_Lemma   = fstar_refl_data_const "C_Lemma"
let ref_C_Unknown = fstar_refl_data_const "C_Unknown"

(* inductives & sigelts *)
let ref_Sg_Let         = fstar_refl_data_const "Sg_Let"
let ref_Sg_Inductive   = fstar_refl_data_const "Sg_Inductive"
let ref_Sg_Constructor = fstar_refl_data_const "Sg_Constructor"
let ref_Unk            = fstar_refl_data_const "Unk"

(* exp *)
let ref_E_Unit = fstar_refl_data_const "Unit"
let ref_E_Var = fstar_refl_data_const "Var"
let ref_E_Mult = fstar_refl_data_const "Mult"
let t_exp = tconst (Ident.lid_of_path ["FStar"; "Reflection"; "Data"; "exp"] Range.dummyRange)

(* Should not be here *)
let ord_Lt_lid = Ident.lid_of_path (["FStar"; "Order"; "Lt"]) Range.dummyRange
let ord_Eq_lid = Ident.lid_of_path (["FStar"; "Order"; "Eq"]) Range.dummyRange
let ord_Gt_lid = Ident.lid_of_path (["FStar"; "Order"; "Gt"]) Range.dummyRange
let ord_Lt = tdataconstr ord_Lt_lid
let ord_Eq = tdataconstr ord_Eq_lid
let ord_Gt = tdataconstr ord_Gt_lid
let ord_Lt_fv = lid_as_fv ord_Lt_lid delta_constant (Some Data_ctor)
let ord_Eq_fv = lid_as_fv ord_Eq_lid delta_constant (Some Data_ctor)
let ord_Gt_fv = lid_as_fv ord_Gt_lid delta_constant (Some Data_ctor)
