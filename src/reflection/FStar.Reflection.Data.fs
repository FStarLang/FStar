#light "off"
module FStar.Reflection.Data

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

type pattern =
    | Pat_Constant of vconst
    | Pat_Cons     of fv * list<pattern>
    | Pat_Var      of bv
    | Pat_Wild     of bv

type branch = pattern * term

type aqualv =
    | Q_Implicit
    | Q_Explicit

type argv = term * aqualv

type term_view =
    | Tv_Var    of binder
    | Tv_FVar   of fv
    | Tv_App    of term * argv
    | Tv_Abs    of binder * term
    | Tv_Arrow  of binder * comp
    | Tv_Type   of unit
    | Tv_Refine of binder * term
    | Tv_Const  of vconst
    | Tv_Uvar   of Z.t * typ
    | Tv_Let    of binder * term * term
    | Tv_Match  of term * list<branch>
    | Tv_Unknown

type comp_view =
    | C_Total of typ
    | C_Lemma of term * term
    | C_Unknown

// See ulib/FStar.Reflection.Syntax.fst for explanations of these two
type ctor =
    | Ctor of  name * typ
type sigelt_view =
    | Sg_Inductive of name * list<binder> * typ * list<ctor>
    | Sg_Let of fv * typ * term
    | Unk


(* Contains all lids and terms needed for embedding/unembedding *)

type refl_constant = {
    lid : FStar.Ident.lid;
    t : term;
}

let fstar_refl_lid s = Ident.lid_of_path (["FStar"; "Reflection"]@s) Range.dummyRange

let fstar_refl_basic_lid  s = fstar_refl_lid ["Basic";  s]
let fstar_refl_syntax_lid s = fstar_refl_lid ["Syntax"; s]
let fstar_refl_types_lid  s = fstar_refl_lid ["Types";  s]
let fstar_refl_data_lid   s = fstar_refl_lid ["Data";   s]

let fstar_refl_data_const s =
    let lid = fstar_refl_data_lid s in
    { lid = lid ; t = tdataconstr lid }

let mk_refl_types_lid_as_term  (s:string) = tconst (fstar_refl_types_lid s)
let mk_refl_syntax_lid_as_term (s:string) = tconst (fstar_refl_syntax_lid s)
let mk_refl_data_lid_as_term   (s:string) = tconst (fstar_refl_data_lid s)

let fstar_refl_inspect_lid = fstar_refl_basic_lid "inspect"
let fstar_refl_inspect     = fvar fstar_refl_inspect_lid (Delta_defined_at_level 1) None
let fstar_refl_pack_lid    = fstar_refl_basic_lid "pack"
let fstar_refl_pack        = fvar fstar_refl_pack_lid (Delta_defined_at_level 1) None
let fstar_refl_pack_fv_lid = fstar_refl_basic_lid "pack_fv"
let fstar_refl_pack_fv     = fvar fstar_refl_pack_fv_lid (Delta_defined_at_level 1) None

(* types *)
let fstar_refl_aqualv    = mk_refl_data_lid_as_term "aqualv"
let fstar_refl_env       = mk_refl_types_lid_as_term "env"
let fstar_refl_fv        = mk_refl_types_lid_as_term "fv"
let fstar_refl_comp      = mk_refl_types_lid_as_term "comp"
let fstar_refl_comp_view = mk_refl_data_lid_as_term "comp_view"
let fstar_refl_binder    = mk_refl_types_lid_as_term "binder"
let fstar_refl_term_view = mk_refl_data_lid_as_term "term_view"
let fstar_refl_ctor      = mk_refl_data_lid_as_term "ctor"
let fstar_refl_pattern   = mk_refl_data_lid_as_term "pattern"
let fstar_refl_branch    = mk_refl_data_lid_as_term "branch"

(* quals *)
let ref_Q_Explicit = fstar_refl_data_const "Q_Explicit"
let ref_Q_Implicit = fstar_refl_data_const "Q_Implicit"

(* const *)
let ref_C_Unit   = fstar_refl_data_const "C_Unit"
let ref_C_True   = fstar_refl_data_const "C_True"
let ref_C_False  = fstar_refl_data_const "C_False"
let ref_C_Int    = fstar_refl_data_const "C_Int"
let ref_C_String = fstar_refl_data_const "C_String"

(* pattern *)
let ref_Pat_Constant = fstar_refl_data_const "Pat_Constant"
let ref_Pat_Cons     = fstar_refl_data_const "Pat_Cons"
let ref_Pat_Var      = fstar_refl_data_const "Pat_Var"
let ref_Pat_Wild     = fstar_refl_data_const "Pat_Wild"

(* term_view *)
let ref_Tv_Var     = fstar_refl_data_const "Tv_Var"
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
let ref_Tv_Unknown = fstar_refl_data_const "Tv_Unknown"

(* comp_view *)
let ref_C_Total   = fstar_refl_data_const "C_Total"
let ref_C_Lemma   = fstar_refl_data_const "C_Lemma"
let ref_C_Unknown = fstar_refl_data_const "C_Unknown"

(* inductives & sigelts *)
let ref_Sg_Inductive = fstar_refl_data_const "Sg_Inductive"
let ref_Sg_Let       = fstar_refl_data_const "Sg_Let"
let ref_Unk          = fstar_refl_data_const "Unk"
let ref_Ctor         = fstar_refl_data_const "Ctor"

(* Should not be here *)
let ord_Lt_lid = Ident.lid_of_path (["FStar"; "Order"; "Lt"]) Range.dummyRange
let ord_Eq_lid = Ident.lid_of_path (["FStar"; "Order"; "Eq"]) Range.dummyRange
let ord_Gt_lid = Ident.lid_of_path (["FStar"; "Order"; "Gt"]) Range.dummyRange
let ord_Lt = tdataconstr ord_Lt_lid
let ord_Eq = tdataconstr ord_Eq_lid
let ord_Gt = tdataconstr ord_Gt_lid
