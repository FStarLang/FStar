#light "off"
module FStar.Reflection.Data

open FStar.Syntax.Syntax
module Ident = FStar.Ident
module Range = FStar.Range

type vconst =
    | C_Unit
    | C_Int of int
    | C_True
    | C_False

type term_view =
    | Tv_Var    of binder
    | Tv_FVar   of fv
    | Tv_App    of term * term
    | Tv_Abs    of binder * term
    | Tv_Arrow  of binder * term
    | Tv_Type   of unit
    | Tv_Refine of binder * term
    | Tv_Const  of vconst
    | Tv_Unknown

type norm_step =
    | Simpl
    | WHNF
    | Primops
    | Delta

let fstar_refl_lid s = Ident.lid_of_path (["FStar"; "Reflection"]@s) Range.dummyRange

let lid_as_tm l = lid_as_fv l Delta_constant None |> fv_to_tm // Move to syntax util?
let lid_as_data_tm l = fv_to_tm (lid_as_fv l Delta_constant (Some Data_ctor))

let fstar_refl_types_lid s = fstar_refl_lid ["Types"; s]
let fstar_refl_syntax_lid s = fstar_refl_lid ["Syntax"; s]

let mk_refl_types_lid_as_term (s:string) = lid_as_tm (fstar_refl_types_lid s)
let mk_refl_syntax_lid_as_term (s:string) = lid_as_tm (fstar_refl_syntax_lid s)
let fstar_refl_lid_as_data_tm s = lid_as_data_tm (fstar_refl_lid s)

(* abstract types *)
let fstar_refl_term      = mk_refl_types_lid_as_term "term"
let fstar_refl_env       = mk_refl_types_lid_as_term "env"
let fstar_refl_fvar      = mk_refl_types_lid_as_term "fv" //TODO: be consistent
let fstar_refl_binder    = mk_refl_types_lid_as_term "binder" // TODO:  just bv, binder = bv * bool
let fstar_refl_binders   = mk_refl_syntax_lid_as_term "binders"
let fstar_refl_term_view = mk_refl_syntax_lid_as_term "term_view"

(* term_view *)
let ref_Tv_Var_lid     = fstar_refl_syntax_lid "Tv_Var"
let ref_Tv_FVar_lid    = fstar_refl_syntax_lid "Tv_FVar"
let ref_Tv_App_lid     = fstar_refl_syntax_lid "Tv_App"
let ref_Tv_Abs_lid     = fstar_refl_syntax_lid "Tv_Abs"
let ref_Tv_Arrow_lid   = fstar_refl_syntax_lid "Tv_Arrow"
let ref_Tv_Type_lid    = fstar_refl_syntax_lid "Tv_Type"
let ref_Tv_Refine_lid  = fstar_refl_syntax_lid "Tv_Refine"
let ref_Tv_Const_lid   = fstar_refl_syntax_lid "Tv_Const"
let ref_Tv_Unknown_lid = fstar_refl_syntax_lid "Tv_Unknown"

let ref_Tv_Var     = lid_as_data_tm ref_Tv_Var_lid
let ref_Tv_FVar    = lid_as_data_tm ref_Tv_FVar_lid
let ref_Tv_App     = lid_as_data_tm ref_Tv_App_lid
let ref_Tv_Abs     = lid_as_data_tm ref_Tv_Abs_lid
let ref_Tv_Arrow   = lid_as_data_tm ref_Tv_Arrow_lid
let ref_Tv_Type    = lid_as_data_tm ref_Tv_Type_lid
let ref_Tv_Refine  = lid_as_data_tm ref_Tv_Refine_lid
let ref_Tv_Const   = lid_as_data_tm ref_Tv_Const_lid
let ref_Tv_Unknown = lid_as_data_tm ref_Tv_Unknown_lid

(* const *)
let ref_C_Unit_lid  = fstar_refl_syntax_lid "C_Unit"
let ref_C_True_lid  = fstar_refl_syntax_lid "C_True"
let ref_C_False_lid = fstar_refl_syntax_lid "C_False"
let ref_C_Int_lid   = fstar_refl_syntax_lid "C_Int"

let ref_C_Unit   = lid_as_data_tm ref_C_Unit_lid
let ref_C_True   = lid_as_data_tm ref_C_True_lid
let ref_C_False  = lid_as_data_tm ref_C_False_lid
let ref_C_Int    = lid_as_data_tm ref_C_Int_lid

(* assumed functions *)

(* FStar.Order, probably a bad place for this *)
type order = | Lt | Eq | Gt

let ord_Lt_lid = Ident.lid_of_path (["FStar"; "Order"; "Lt"]) Range.dummyRange
let ord_Eq_lid = Ident.lid_of_path (["FStar"; "Order"; "Eq"]) Range.dummyRange
let ord_Gt_lid = Ident.lid_of_path (["FStar"; "Order"; "Gt"]) Range.dummyRange
let ord_Lt = lid_as_data_tm ord_Lt_lid
let ord_Eq = lid_as_data_tm ord_Eq_lid
let ord_Gt = lid_as_data_tm ord_Gt_lid

let fstar_refl_norm_step = mk_refl_syntax_lid_as_term "norm_step"

let ref_Simpl_lid      = fstar_refl_syntax_lid "Simpl"
let ref_WHNF_lid       = fstar_refl_syntax_lid "WHNF"
let ref_Primops_lid    = fstar_refl_syntax_lid "Primops"
let ref_Delta_lid      = fstar_refl_syntax_lid "Delta"

let ref_Simpl          = lid_as_data_tm ref_Simpl_lid
let ref_WHNF           = lid_as_data_tm ref_WHNF_lid
let ref_Primops        = lid_as_data_tm ref_Primops_lid
let ref_Delta          = lid_as_data_tm ref_Delta_lid

module TC = FStar.TypeChecker.Common
let t_binder = TC.tabbrev <| fstar_refl_types_lid "binder"
let t_term = TC.tabbrev <| fstar_refl_types_lid "term"
let t_fv = TC.tabbrev <| fstar_refl_types_lid "fv"
let t_binders = TC.tabbrev <| fstar_refl_syntax_lid "binders"

let t_norm_step = TC.tabbrev <| fstar_refl_syntax_lid "norm_step"
