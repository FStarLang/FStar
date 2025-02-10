(*
   Copyright 2008-2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Reflection.V1.Constants

open FStarC.Effect
open FStarC.Syntax.Syntax
open FStar.List.Tot.Base
module Ident = FStarC.Ident
module Range = FStarC.Range.Type

(* Contains all lids and terms needed for embedding/unembedding *)

type refl_constant = {
    lid : FStarC.Ident.lid;
    fv : fv;
    t : term;
}

let refl_constant_lid rc = rc.lid
let refl_constant_term rc = rc.t
let fstar_refl_lid s = Ident.lid_of_path (["FStar"; "Stubs"; "Reflection"]@s) Range.dummyRange

let fstar_refl_types_lid     s = fstar_refl_lid ["Types";     s]
let fstar_refl_builtins_lid  s = fstar_refl_lid ["V1"; "Builtins";  s]
let fstar_refl_data_lid      s = fstar_refl_lid ["V1"; "Data";      s]

let fstar_refl_data_const s =
    let lid = fstar_refl_data_lid s in
    { lid = lid
    ; fv  = lid_as_fv lid (Some Data_ctor)
    ; t   = tdataconstr lid
    }

let mk_refl_types_lid_as_term  (s:string) = tconst  (fstar_refl_types_lid s)
let mk_refl_types_lid_as_fv    (s:string) = fvconst (fstar_refl_types_lid s)
let mk_refl_data_lid_as_term   (s:string) = tconst  (fstar_refl_data_lid s)
let mk_refl_data_lid_as_fv     (s:string) = fvconst (fstar_refl_data_lid s)

let mk_inspect_pack_pair s =
    let inspect_lid = fstar_refl_builtins_lid ("inspect" ^ s) in
    let pack_lid    = fstar_refl_builtins_lid ("pack" ^ s) in
    let inspect_fv  = lid_as_fv inspect_lid None in
    let pack_fv     = lid_as_fv pack_lid    None in
    let inspect     = { lid = inspect_lid ; fv = inspect_fv ; t = fv_to_tm inspect_fv } in
    let pack        = { lid = pack_lid    ; fv = pack_fv    ; t = fv_to_tm pack_fv } in
    (inspect, pack)

let fstar_refl_inspect_ln      , fstar_refl_pack_ln     = mk_inspect_pack_pair "_ln"
let fstar_refl_inspect_fv      , fstar_refl_pack_fv     = mk_inspect_pack_pair "_fv"
let fstar_refl_inspect_bv      , fstar_refl_pack_bv     = mk_inspect_pack_pair "_bv"
let fstar_refl_inspect_binder  , fstar_refl_pack_binder = mk_inspect_pack_pair "_binder"
let fstar_refl_inspect_comp    , fstar_refl_pack_comp   = mk_inspect_pack_pair "_comp"
let fstar_refl_inspect_sigelt  , fstar_refl_pack_sigelt = mk_inspect_pack_pair "_sigelt"
let fstar_refl_inspect_lb      , fstar_refl_pack_lb     = mk_inspect_pack_pair "_lb"
let fstar_refl_inspect_universe, fstar_refl_pack_universe  = mk_inspect_pack_pair "_universe"

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
let fstar_refl_letbinding       = mk_refl_types_lid_as_term "letbinding"
let fstar_refl_letbinding_fv    = mk_refl_types_lid_as_fv   "letbinding"
let fstar_refl_ident            = mk_refl_types_lid_as_term "ident"
let fstar_refl_ident_fv         = mk_refl_types_lid_as_fv   "ident"
let fstar_refl_univ_name        = mk_refl_types_lid_as_term "univ_name"
let fstar_refl_univ_name_fv     = mk_refl_types_lid_as_fv   "univ_name"
let fstar_refl_optionstate      = mk_refl_types_lid_as_term "optionstate"
let fstar_refl_optionstate_fv   = mk_refl_types_lid_as_fv   "optionstate"
let fstar_refl_universe         = mk_refl_types_lid_as_term "universe"
let fstar_refl_universe_fv      = mk_refl_types_lid_as_fv   "universe"

(* auxiliary types *)
let fstar_refl_aqualv           = mk_refl_data_lid_as_term "aqualv"
let fstar_refl_aqualv_fv        = mk_refl_data_lid_as_fv   "aqualv"
let fstar_refl_comp_view        = mk_refl_data_lid_as_term "comp_view"
let fstar_refl_comp_view_fv     = mk_refl_data_lid_as_fv   "comp_view"
let fstar_refl_term_view        = mk_refl_data_lid_as_term "term_view"
let fstar_refl_term_view_fv     = mk_refl_data_lid_as_fv   "term_view"
let fstar_refl_pattern          = mk_refl_data_lid_as_term "pattern"
let fstar_refl_pattern_fv       = mk_refl_data_lid_as_fv   "pattern"
let fstar_refl_branch           = mk_refl_data_lid_as_term "branch"
let fstar_refl_branch_fv        = mk_refl_data_lid_as_fv   "branch"
let fstar_refl_bv_view          = mk_refl_data_lid_as_term "bv_view"
let fstar_refl_bv_view_fv       = mk_refl_data_lid_as_fv   "bv_view"
let fstar_refl_binder_view      = mk_refl_data_lid_as_term "binder_view"
let fstar_refl_binder_view_fv   = mk_refl_data_lid_as_fv   "binder_view"
let fstar_refl_vconst           = mk_refl_data_lid_as_term "vconst"
let fstar_refl_vconst_fv        = mk_refl_data_lid_as_fv   "vconst"
let fstar_refl_lb_view          = mk_refl_data_lid_as_term "lb_view"
let fstar_refl_lb_view_fv       = mk_refl_data_lid_as_fv   "lb_view"
let fstar_refl_sigelt_view      = mk_refl_data_lid_as_term "sigelt_view"
let fstar_refl_sigelt_view_fv   = mk_refl_data_lid_as_fv   "sigelt_view"
let fstar_refl_qualifier        = mk_refl_data_lid_as_term "qualifier"
let fstar_refl_qualifier_fv     = mk_refl_data_lid_as_fv   "qualifier"
let fstar_refl_universe_view    = mk_refl_data_lid_as_term "universe_view"
let fstar_refl_universe_view_fv = mk_refl_data_lid_as_fv   "universe_view"

(* bv_view, this is a record constructor *)

let ref_Mk_bv =
    let lid = fstar_refl_data_lid "Mkbv_view" in
    let attr = Record_ctor (fstar_refl_data_lid "bv_view", [
                                Ident.mk_ident ("bv_ppname", Range.dummyRange);
                                Ident.mk_ident ("bv_index" , Range.dummyRange)]) in
    let fv = lid_as_fv lid (Some attr) in
    { lid = lid
    ; fv  = fv
    ; t   = fv_to_tm fv
    }

let ref_Mk_binder =
  let lid = fstar_refl_data_lid "Mkbinder_view" in
  let attr = Record_ctor (fstar_refl_data_lid "binder_view", [
                            Ident.mk_ident ("binder_bv", Range.dummyRange);
                            Ident.mk_ident ("binder_qual", Range.dummyRange);
                            Ident.mk_ident ("binder_attrs", Range.dummyRange);
                            Ident.mk_ident ("binder_sort"  , Range.dummyRange)]) in
  let fv = lid_as_fv lid (Some attr) in
  { lid = lid;
    fv = fv;
    t = fv_to_tm fv }

let ref_Mk_lb =
    let lid = fstar_refl_data_lid "Mklb_view" in
    let attr = Record_ctor (fstar_refl_data_lid "lb_view", [
                                Ident.mk_ident ("lb_fv"  , Range.dummyRange);
                                Ident.mk_ident ("lb_us"  , Range.dummyRange);
                                Ident.mk_ident ("lb_typ" , Range.dummyRange);
                                Ident.mk_ident ("lb_def" , Range.dummyRange)
                                ]) in
    let fv = lid_as_fv lid (Some attr) in
    { lid = lid
    ; fv  = fv
    ; t   = fv_to_tm fv
    }

(* quals *)
let ref_Q_Explicit  = fstar_refl_data_const "Q_Explicit"
let ref_Q_Implicit  = fstar_refl_data_const "Q_Implicit"
let ref_Q_Meta      = fstar_refl_data_const "Q_Meta"

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
let ref_Pat_Dot_Term = fstar_refl_data_const "Pat_Dot_Term"

(* universe_view *)
let ref_Uv_Zero    = fstar_refl_data_const "Uv_Zero"
let ref_Uv_Succ    = fstar_refl_data_const "Uv_Succ"
let ref_Uv_Max     = fstar_refl_data_const "Uv_Max"
let ref_Uv_BVar    = fstar_refl_data_const "Uv_BVar"
let ref_Uv_Name    = fstar_refl_data_const "Uv_Name"
let ref_Uv_Unif    = fstar_refl_data_const "Uv_Unif"
let ref_Uv_Unk     = fstar_refl_data_const "Uv_Unk"

(* term_view *)
let ref_Tv_Var     = fstar_refl_data_const "Tv_Var"
let ref_Tv_BVar    = fstar_refl_data_const "Tv_BVar"
let ref_Tv_FVar    = fstar_refl_data_const "Tv_FVar"
let ref_Tv_UInst   = fstar_refl_data_const "Tv_UInst"
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
let ref_Tv_Unsupp  = fstar_refl_data_const "Tv_Unsupp"

(* comp_view *)
let ref_C_Total   = fstar_refl_data_const "C_Total"
let ref_C_GTotal  = fstar_refl_data_const "C_GTotal"
let ref_C_Lemma   = fstar_refl_data_const "C_Lemma"
let ref_C_Eff     = fstar_refl_data_const "C_Eff"

(* inductives & sigelts *)
let ref_Sg_Let         = fstar_refl_data_const "Sg_Let"
let ref_Sg_Inductive   = fstar_refl_data_const "Sg_Inductive"
let ref_Sg_Val         = fstar_refl_data_const "Sg_Val"
let ref_Unk            = fstar_refl_data_const "Unk"

(* qualifiers *)
let ref_qual_Assumption                       = fstar_refl_data_const "Assumption"
let ref_qual_InternalAssumption               = fstar_refl_data_const "InternalAssumption"
let ref_qual_New                              = fstar_refl_data_const "New"
let ref_qual_Private                          = fstar_refl_data_const "Private"
let ref_qual_Unfold_for_unification_and_vcgen = fstar_refl_data_const "Unfold_for_unification_and_vcgen"
let ref_qual_Visible_default                  = fstar_refl_data_const "Visible_default"
let ref_qual_Irreducible                      = fstar_refl_data_const "Irreducible"
let ref_qual_Inline_for_extraction            = fstar_refl_data_const "Inline_for_extraction"
let ref_qual_NoExtract                        = fstar_refl_data_const "NoExtract"
let ref_qual_Noeq                             = fstar_refl_data_const "Noeq"
let ref_qual_Unopteq                          = fstar_refl_data_const "Unopteq"
let ref_qual_TotalEffect                      = fstar_refl_data_const "TotalEffect"
let ref_qual_Logic                            = fstar_refl_data_const "Logic"
let ref_qual_Reifiable                        = fstar_refl_data_const "Reifiable"
let ref_qual_Reflectable                      = fstar_refl_data_const "Reflectable"
let ref_qual_Discriminator                    = fstar_refl_data_const "Discriminator"
let ref_qual_Projector                        = fstar_refl_data_const "Projector"
let ref_qual_RecordType                       = fstar_refl_data_const "RecordType"
let ref_qual_RecordConstructor                = fstar_refl_data_const "RecordConstructor"
let ref_qual_Action                           = fstar_refl_data_const "Action"
let ref_qual_ExceptionConstructor             = fstar_refl_data_const "ExceptionConstructor"
let ref_qual_HasMaskedEffect                  = fstar_refl_data_const "HasMaskedEffect"
let ref_qual_Effect                           = fstar_refl_data_const "Effect"
let ref_qual_OnlyName                         = fstar_refl_data_const "OnlyName"
