#light "off"
module FStar.Reflection.Data

open FStar.Syntax.Syntax
module Ident = FStar.Ident
module Range = FStar.Range

type name = list<string>
type typ  = term
type binders = list<binder>

type vconst =
    | C_Unit
    | C_Int of int
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
    | Tv_Uvar   of int * typ
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

let fstar_refl_lid s = Ident.lid_of_path (["FStar"; "Reflection"]@s) Range.dummyRange

let fstar_refl_basic_lid s = fstar_refl_lid ["Basic"; s]
let fstar_refl_types_lid s = fstar_refl_lid ["Types"; s]
let fstar_refl_syntax_lid s = fstar_refl_lid ["Syntax"; s]
let fstar_refl_data_lid s  = fstar_refl_lid ["Data"; s]

let mk_refl_types_lid_as_term (s:string) = tconst (fstar_refl_types_lid s)
let mk_refl_syntax_lid_as_term (s:string) = tconst (fstar_refl_syntax_lid s)
let mk_refl_data_lid_as_term (s:string)  = tconst (fstar_refl_data_lid s)
let fstar_refl_tdataconstr s = tdataconstr (fstar_refl_lid s)

(* types *)
let fstar_refl_aqualv    = mk_refl_data_lid_as_term "aqualv"
let fstar_refl_env       = mk_refl_types_lid_as_term "env"
let fstar_refl_fvar      = mk_refl_types_lid_as_term "fv" //TODO: be consistent
let fstar_refl_comp      = mk_refl_types_lid_as_term "comp"
let fstar_refl_comp_view = mk_refl_types_lid_as_term "comp_view"
let fstar_refl_binder    = mk_refl_types_lid_as_term "binder" // TODO:  just bv, binder = bv * bool
let fstar_refl_binders   = mk_refl_types_lid_as_term "binders"
let fstar_refl_term_view = mk_refl_types_lid_as_term "term_view"
let fstar_refl_sigelt    = mk_refl_types_lid_as_term "sigelt"
let fstar_refl_ctor      = mk_refl_types_lid_as_term "ctor"
let fstar_refl_pattern   = mk_refl_syntax_lid_as_term "pattern"
let fstar_refl_branch    = mk_refl_types_lid_as_term "branch"

(* quals *)
let ref_Q_Explicit_lid   = fstar_refl_data_lid "Q_Explicit"
let ref_Q_Implicit_lid   = fstar_refl_data_lid "Q_Implicit"
let ref_Q_Explicit       = tdataconstr ref_Q_Explicit_lid
let ref_Q_Implicit       = tdataconstr ref_Q_Implicit_lid

(* const *)
let ref_C_Unit_lid  = fstar_refl_data_lid "C_Unit"
let ref_C_True_lid  = fstar_refl_data_lid "C_True"
let ref_C_False_lid = fstar_refl_data_lid "C_False"
let ref_C_Int_lid   = fstar_refl_data_lid "C_Int"
let ref_C_String_lid = fstar_refl_data_lid "C_String"

let ref_C_Unit   = tdataconstr ref_C_Unit_lid
let ref_C_True   = tdataconstr ref_C_True_lid
let ref_C_False  = tdataconstr ref_C_False_lid
let ref_C_Int    = tdataconstr ref_C_Int_lid
let ref_C_String = tdataconstr ref_C_String_lid

(* pattern *)
let ref_Pat_Constant_lid   = fstar_refl_data_lid "Pat_Constant"
let ref_Pat_Cons_lid       = fstar_refl_data_lid "Pat_Cons"
let ref_Pat_Var_lid        = fstar_refl_data_lid "Pat_Var"
let ref_Pat_Wild_lid       = fstar_refl_data_lid "Pat_Wild"

let ref_Pat_Constant   = tdataconstr ref_Pat_Constant_lid
let ref_Pat_Cons       = tdataconstr ref_Pat_Cons_lid
let ref_Pat_Var        = tdataconstr ref_Pat_Var_lid
let ref_Pat_Wild       = tdataconstr ref_Pat_Wild_lid

(* term_view *)
let ref_Tv_Var_lid     = fstar_refl_data_lid "Tv_Var"
let ref_Tv_FVar_lid    = fstar_refl_data_lid "Tv_FVar"
let ref_Tv_App_lid     = fstar_refl_data_lid "Tv_App"
let ref_Tv_Abs_lid     = fstar_refl_data_lid "Tv_Abs"
let ref_Tv_Arrow_lid   = fstar_refl_data_lid "Tv_Arrow"
let ref_Tv_Type_lid    = fstar_refl_data_lid "Tv_Type"
let ref_Tv_Refine_lid  = fstar_refl_data_lid "Tv_Refine"
let ref_Tv_Const_lid   = fstar_refl_data_lid "Tv_Const"
let ref_Tv_Uvar_lid    = fstar_refl_data_lid "Tv_Uvar"
let ref_Tv_Let_lid     = fstar_refl_data_lid "Tv_Let"
let ref_Tv_Match_lid   = fstar_refl_data_lid "Tv_Match"
let ref_Tv_Unknown_lid = fstar_refl_data_lid "Tv_Unknown"

let ref_Tv_Var     = tdataconstr ref_Tv_Var_lid
let ref_Tv_FVar    = tdataconstr ref_Tv_FVar_lid
let ref_Tv_App     = tdataconstr ref_Tv_App_lid
let ref_Tv_Abs     = tdataconstr ref_Tv_Abs_lid
let ref_Tv_Arrow   = tdataconstr ref_Tv_Arrow_lid
let ref_Tv_Type    = tdataconstr ref_Tv_Type_lid
let ref_Tv_Refine  = tdataconstr ref_Tv_Refine_lid
let ref_Tv_Const   = tdataconstr ref_Tv_Const_lid
let ref_Tv_Uvar    = tdataconstr ref_Tv_Uvar_lid
let ref_Tv_Let     = tdataconstr ref_Tv_Let_lid
let ref_Tv_Match   = tdataconstr ref_Tv_Match_lid
let ref_Tv_Unknown = tdataconstr ref_Tv_Unknown_lid

(* comp_view *)
let ref_C_Total_lid     = fstar_refl_data_lid "C_Total"
let ref_C_Lemma_lid     = fstar_refl_data_lid "C_Lemma"
let ref_C_Unknown_lid   = fstar_refl_data_lid "C_Unknown"

let ref_C_Total         = tdataconstr ref_C_Total_lid
let ref_C_Lemma         = tdataconstr ref_C_Lemma_lid
let ref_C_Unknown       = tdataconstr ref_C_Unknown_lid

(* inductives & sigelts *)
let ref_Sg_Inductive_lid = fstar_refl_data_lid "Sg_Inductive"
let ref_Sg_Let_lid       = fstar_refl_data_lid "Sg_Let"
let ref_Unk_lid          = fstar_refl_data_lid "Unk"
let ref_Ctor_lid         = fstar_refl_data_lid "Ctor"
let ref_Sg_Inductive = tdataconstr ref_Sg_Inductive_lid
let ref_Sg_Let       = tdataconstr ref_Sg_Let_lid
let ref_Unk          = tdataconstr ref_Unk_lid
let ref_Ctor         = tdataconstr ref_Ctor_lid

let t_binder = tabbrev <| fstar_refl_types_lid "binder"
let t_term = tabbrev <| fstar_refl_types_lid "term"
let t_fv = tabbrev <| fstar_refl_types_lid "fv"
let t_binders = tabbrev <| fstar_refl_types_lid "binders"

let ord_Lt_lid = Ident.lid_of_path (["FStar"; "Order"; "Lt"]) Range.dummyRange
let ord_Eq_lid = Ident.lid_of_path (["FStar"; "Order"; "Eq"]) Range.dummyRange
let ord_Gt_lid = Ident.lid_of_path (["FStar"; "Order"; "Gt"]) Range.dummyRange
let ord_Lt = tdataconstr ord_Lt_lid
let ord_Eq = tdataconstr ord_Eq_lid
let ord_Gt = tdataconstr ord_Gt_lid
