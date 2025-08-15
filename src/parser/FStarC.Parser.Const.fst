(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR C  ONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Parser.Const

open FStarC
open FStarC.Effect
open FStarC.Ident
open FStarC.Range.Type
open FStarC.Const
open FStarC.List
module U = FStarC.Util
include FStarC.Parser.Const.Tuples

let p2l l = lid_of_path l dummyRange

let pconst s              = p2l ["Prims";s]
let psconst s             = p2l ["FStar"; "Pervasives"; s]
let attr s                = p2l ["FStar"; "Attributes"; s]
let psnconst s            = p2l ["FStar"; "Pervasives" ; "Native" ; s]
let prims_lid             = p2l ["Prims"]
let pervasives_native_lid = p2l ["FStar"; "Pervasives"; "Native"]
let pervasives_lid        = p2l ["FStar"; "Pervasives"]
let fstar_ns_lid          = p2l ["FStar"]

(* Primitive types *)
let bool_lid         = pconst "bool"
let unit_lid         = pconst "unit"
let squash_lid       = pconst "squash"
let auto_squash_lid  = pconst "auto_squash"
let string_lid       = pconst "string"
let bytes_lid        = pconst "bytes"
let int_lid          = pconst "int"
let exn_lid          = pconst "exn"
let list_lid         = pconst "list"
let immutable_array_t_lid = p2l ["FStar"; "ImmutableArray"; "Base"; "t"]
let immutable_array_of_list_lid  = p2l ["FStar"; "ImmutableArray"; "Base"; "of_list"]
let immutable_array_length_lid   = p2l ["FStar"; "ImmutableArray"; "Base"; "length"]
let immutable_array_index_lid    = p2l ["FStar"; "ImmutableArray"; "Base"; "index"]
let eqtype_lid       = pconst "eqtype"
let option_lid       = psnconst "option"
let either_lid       = psconst "either"
let pattern_lid      = psconst "pattern"
let lex_t_lid        = pconst "lex_t"
let precedes_lid     = pconst "precedes"
let smtpat_lid       = psconst "smt_pat"
let smtpatOr_lid     = psconst "smt_pat_or"
let monadic_lid      = pconst "M"
let spinoff_lid      = psconst "spinoff"
let inl_lid          = psconst "Inl"
let inr_lid          = psconst "Inr"

let int8_lid   = p2l ["FStar"; "Int8"; "t"]
let uint8_lid  = p2l ["FStar"; "UInt8"; "t"]
let int16_lid   = p2l ["FStar"; "Int16"; "t"]
let uint16_lid  = p2l ["FStar"; "UInt16"; "t"]
let int32_lid   = p2l ["FStar"; "Int32"; "t"]
let uint32_lid  = p2l ["FStar"; "UInt32"; "t"]
let int64_lid   = p2l ["FStar"; "Int64"; "t"]
let uint64_lid  = p2l ["FStar"; "UInt64"; "t"]
let sizet_lid  = p2l ["FStar"; "SizeT"; "t"]

let salloc_lid = p2l ["FStar"; "ST"; "salloc"]
let swrite_lid = p2l ["FStar"; "ST"; "op_Colon_Equals"]
let sread_lid = p2l ["FStar"; "ST"; "op_Bang"]

let max_lid = p2l ["max"]

let real_lid  = p2l ["FStar"; "Real"; "real"]

let float_lid  = p2l ["FStar"; "Float"; "float"]

let char_lid  = p2l ["FStar"; "Char"; "char"]

let heap_lid   = p2l ["FStar"; "Heap"; "heap"]

let logical_lid = pconst "logical"
let prop_lid    = pconst "prop"

let smt_theory_symbol_attr_lid = pconst "smt_theory_symbol"

let true_lid   = pconst "l_True"
let false_lid  = pconst "l_False"
let and_lid    = pconst "l_and"
let or_lid     = pconst "l_or"
let not_lid    = pconst "l_not"
let imp_lid    = pconst "l_imp"
let iff_lid    = pconst "l_iff"
let ite_lid    = pconst "l_ITE"
let exists_lid = pconst "l_Exists"
let forall_lid = pconst "l_Forall"
let haseq_lid  = pconst "hasEq"
let b2t_lid    = pconst "b2t" (* coercion from boolean to type *)
let admit_lid  = pconst "admit"
let magic_lid  = pconst "magic"
let has_type_lid = pconst "has_type"

(* Constructive variants *)
let c_true_lid      = pconst "trivial"
let empty_type_lid  = pconst "empty"
let c_and_lid       = pconst "pair"
let c_or_lid        = pconst "sum"

(* Various equality predicates *)
let eq2_lid    = pconst  "eq2"
let eq3_lid    = pconst  "op_Equals_Equals_Equals"
let c_eq2_lid  = pconst "equals"

(* Some common term constructors *)
let cons_lid              = pconst  "Cons"
let nil_lid               = pconst  "Nil"
let some_lid              = psnconst  "Some"
let none_lid              = psnconst  "None"
let assume_lid            = pconst  "_assume"
let assert_lid            = pconst  "_assert"
let pure_wp_lid           = pconst "pure_wp"
let pure_wp_monotonic_lid = pconst "pure_wp_monotonic"
let pure_wp_monotonic0_lid = pconst "pure_wp_monotonic0"
let trivial_pure_post_lid = psconst "trivial_pure_post"
let pure_assert_wp_lid    = pconst "pure_assert_wp0"
let pure_assume_wp_lid    = pconst "pure_assume_wp0"
let assert_norm_lid       = p2l ["FStar"; "Pervasives"; "assert_norm"]
(* list_append_lid is needed to desugar @ in the compiler *)
let list_append_lid       = p2l ["FStar"; "List"; "append"]
(* list_tot_append_lid is used to desugar @ everywhere else *)
let list_tot_append_lid   = p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let id_lid                = psconst "id"

let seq_cons_lid              = p2l ["FStar"; "Seq"; "Base"; "cons"]
let seq_empty_lid             = p2l ["FStar"; "Seq"; "Base"; "empty"]

/// Constants from FStar.Char
let c2l s = p2l ["FStar"; "Char"; s]
let char_u32_of_char = c2l "u32_of_char"

/// Constants from FStar.String
let s2l n = p2l ["FStar"; "String"; n]
let string_list_of_string_lid = s2l "list_of_string"
let string_string_of_list_lid = s2l "string_of_list"
let string_make_lid = s2l "make"
let string_split_lid = s2l "split"
let string_concat_lid = s2l "concat"
let string_compare_lid = s2l "compare"
let string_lowercase_lid = s2l "lowercase"
let string_uppercase_lid = s2l "uppercase"
let string_index_lid = s2l "index"
let string_index_of_lid = s2l "index_of"
let string_sub_lid = s2l "sub"
let prims_strcat_lid = pconst "strcat"
let prims_op_Hat_lid = pconst "op_Hat"

let let_in_typ      = p2l ["Prims"; "Let"]
let string_of_int_lid = p2l ["Prims"; "string_of_int"]
let string_of_bool_lid = p2l ["Prims"; "string_of_bool"]
let int_of_string_lid = p2l ["FStar"; "Parse"; "int_of_string"]
let bool_of_string_lid = p2l ["FStar"; "Parse"; "bool_of_string"]
let string_compare = p2l ["FStar"; "String"; "compare"]
let order_lid       = p2l ["FStar"; "Order"; "order"]
let vconfig_lid     = p2l ["FStar"; "Stubs"; "VConfig"; "vconfig"]
let mkvconfig_lid   = p2l ["FStar"; "Stubs"; "VConfig"; "Mkvconfig"]

(* Primitive operators *)
let op_Eq              = pconst "op_Equality"
let op_notEq           = pconst "op_disEquality"
let op_LT              = pconst "op_LessThan"
let op_LTE             = pconst "op_LessThanOrEqual"
let op_GT              = pconst "op_GreaterThan"
let op_GTE             = pconst "op_GreaterThanOrEqual"
let op_Subtraction     = pconst "op_Subtraction"
let op_Minus           = pconst "op_Minus"
let op_Addition        = pconst "op_Addition"
let op_Multiply        = pconst "op_Multiply"
let op_Division        = pconst "op_Division"
let op_Modulus         = pconst "op_Modulus"
let op_And             = pconst "op_AmpAmp"
let op_Or              = pconst "op_BarBar"
let op_Negation        = pconst "op_Negation"
let subtype_of_lid     = pconst "subtype_of"

let real_const  s        = p2l ["FStar";"Real";s]
let real_op_LT           = real_const "op_Less_Dot"
let real_op_LTE          = real_const "op_Less_Equals_Dot"
let real_op_GT           = real_const "op_Greater_Dot"
let real_op_GTE          = real_const "op_Greater_Equals_Dot"
let real_op_Subtraction  = real_const "op_Subtraction_Dot"
let real_op_Addition     = real_const "op_Plus_Dot"
let real_op_Multiply     = real_const "op_Star_Dot"
let real_op_Division     = real_const "op_Slash_Dot"
let real_of_int          = real_const "of_int"


let bvconst s = p2l ["FStar"; "BV"; s]

(* BitVector constants *)
let bv_t_lid = bvconst "bv_t" //redundant
//let bv_zero_vec_lid = bvconst "bv_zero"
//let bv_ones_vec_lid = bvconst "ones_vec"

(* BitVector operators *)
let nat_to_bv_lid      = bvconst "int2bv"
let bv_to_nat_lid      = bvconst "bv2int"
let bv_and_lid         = bvconst "bvand"
let bv_xor_lid         = bvconst "bvxor"
let bv_or_lid          = bvconst "bvor"
let bv_add_lid         = bvconst "bvadd"
let bv_sub_lid         = bvconst "bvsub"
let bv_shift_left_lid  = bvconst "bvshl"
let bv_shift_right_lid = bvconst "bvshr"
let bv_udiv_lid        = bvconst "bvdiv"
let bv_mod_lid         = bvconst "bvmod"
let bv_mul_lid         = bvconst "bvmul"
// shifts, division and multiplication take natural numbers as their second
// arguments, which incurs some encoding overhead. The primed versions bvshl',
// bvshr', bvdiv_unsafe, bvmod_unsafe and bvmul' take a bitvector as the second
// argument instead, which more closely matches SMT-LIB.
let bv_shift_left'_lid = bvconst "bvshl'"
let bv_shift_right'_lid= bvconst "bvshr'"
let bv_udiv_unsafe_lid = bvconst "bvdiv_unsafe"
let bv_mod_unsafe_lid  = bvconst "bvmod_unsafe"
let bv_mul'_lid        = bvconst "bvmul'"

let bv_ult_lid         = bvconst "bvult"
let bv_uext_lid        = bvconst "bv_uext"

(* Array constants *)
let array_lid          = p2l ["FStar"; "Array"; "array"]
let array_of_list_lid = p2l ["FStar"; "Array"; "of_list"]

(* Stateful constants *)
let st_lid       = p2l ["FStar"; "ST"]
let write_lid    = p2l ["FStar"; "ST"; "write"]
let read_lid     = p2l ["FStar"; "ST"; "read"]
let alloc_lid    = p2l ["FStar"; "ST"; "alloc"]
let op_ColonEq   = p2l ["FStar"; "ST"; "op_Colon_Equals"]

(* Constants for sets and ref sets *)
let ref_lid             = p2l ["FStar"; "Heap"; "ref"]
let heap_addr_of_lid    = p2l ["FStar"; "Heap"; "addr_of"]
let set_empty           = p2l ["FStar"; "Set"; "empty"]
let set_singleton       = p2l ["FStar"; "Set"; "singleton"]
let set_union           = p2l ["FStar"; "Set"; "union"]
let fstar_hyperheap_lid = p2l ["FStar"; "HyperHeap"]
let rref_lid            = p2l ["FStar"; "HyperHeap"; "rref"]

(* Other special constants *)
let erased_lid    = p2l ["FStar"; "Ghost"; "erased"]

(* monad constants *)
let effect_PURE_lid  = pconst "PURE"
let effect_Pure_lid  = pconst "Pure"
let effect_Tot_lid   = pconst "Tot"
let effect_Lemma_lid = psconst "Lemma"
let effect_GTot_lid  = pconst "GTot"
let effect_GHOST_lid = pconst "GHOST"
let effect_Ghost_lid = pconst "Ghost"
let effect_DIV_lid   = psconst "DIV"
let effect_Div_lid   = psconst "Div"
let effect_Dv_lid    = psconst "Dv"

(* The "All" monad and its associated symbols.

NOTE: With --MLish and --MLish_effect <module> this is somewhat configurable *)

let ef_base () =
  if Options.ml_ish ()
  then String.split ['.'] <| Options.ml_ish_effect ()
  else ["FStar"; "All"]

let effect_ALL_lid () = p2l <| ef_base () @ ["ALL"]
let effect_ML_lid  () = p2l <| ef_base () @ ["ML"]
let failwith_lid   () = p2l <| ef_base () @ ["failwith"]
let try_with_lid   () = p2l <| ef_base () @ ["try_with"]

let as_requires    = pconst "as_requires"
let as_ensures     = pconst "as_ensures"
let decreases_lid  = pconst "decreases"

let reveal = p2l ["FStar"; "Ghost"; "reveal"]
let hide   = p2l ["FStar"; "Ghost"; "hide"]

(* FStar.Range *)
let labeled_lid    = p2l ["FStar"; "Range"; "labeled"]
let __range_lid    = p2l ["FStar"; "Range"; "__range"]
let range_lid      = p2l ["FStar"; "Range"; "range"] (* this is a sealed version of the above *)
let range_0        = p2l ["FStar"; "Range"; "range_0"]
let mk_range_lid   = p2l ["FStar"; "Range"; "mk_range"]
let __mk_range_lid = p2l ["FStar"; "Range"; "__mk_range"]
let __explode_range_lid = p2l ["FStar"; "Range"; "explode"]
let join_range_lid   = p2l ["FStar"; "Range"; "join_range"]

let guard_free     = pconst "guard_free"
let inversion_lid  = p2l ["FStar"; "Pervasives"; "inversion"]

(* Constants for marking terms with normalization hints *)
let normalize      = psconst "normalize"
let normalize_term = psconst "normalize_term"
let norm           = psconst "norm"

(* lids for normalizer steps *)
let mk_norm_step_lid l = p2l ["FStar"; "NormSteps"; l]
let norm_step_lid         = mk_norm_step_lid "norm_step"
let steps_simpl           = mk_norm_step_lid "simplify"
let steps_weak            = mk_norm_step_lid "weak"
let steps_hnf             = mk_norm_step_lid "hnf"
let steps_primops         = mk_norm_step_lid "primops"
let steps_zeta            = mk_norm_step_lid "zeta"
let steps_zeta_full       = mk_norm_step_lid "zeta_full"
let steps_iota            = mk_norm_step_lid "iota"
let steps_delta           = mk_norm_step_lid "delta"
let steps_reify           = mk_norm_step_lid "reify_"
let steps_norm_debug      = mk_norm_step_lid "norm_debug"
let steps_unfoldonly      = mk_norm_step_lid "delta_only"
let steps_unfoldonce      = mk_norm_step_lid "delta_once"
let steps_unfoldfully     = mk_norm_step_lid "delta_fully"
let steps_unfoldattr      = mk_norm_step_lid "delta_attr"
let steps_unfoldqual      = mk_norm_step_lid "delta_qualifier"
let steps_unfoldnamespace = mk_norm_step_lid "delta_namespace"
let steps_unascribe       = mk_norm_step_lid "unascribe"
let steps_nbe             = mk_norm_step_lid "nbe"
let steps_unmeta          = mk_norm_step_lid "unmeta"

(* attributes *)
let deprecated_attr = pconst "deprecated"
let warn_on_use_attr = pconst "warn_on_use"
let inline_let_attr = attr "inline_let"
let inline_let_vc_attr = attr "inline_let_vc"
let no_inline_let_attr = attr "no_inline_let"
let rename_let_attr = attr "rename_let"
let plugin_attr     = attr "plugin"
let tcnorm_attr    =  attr "tcnorm"
let dm4f_bind_range_attr = attr "dm4f_bind_range"
let must_erase_for_extraction_attr = attr "must_erase_for_extraction"
let strict_on_arguments_attr =  attr "strict_on_arguments"
let resolve_implicits_attr_string = attr "resolve_implicits"
let override_resolve_implicits_handler_lid = attr "override_resolve_implicits_handler"
let handle_smt_goals_attr = attr "handle_smt_goals"
let erasable_attr = attr "erasable"
let fail_attr      = attr "expect_failure"
let fail_lax_attr  = attr "expect_lax_failure"
let unification_tag_lid = attr "defer_to"

let comment_attr = attr "Comment"
let c_inline_attr = attr "CInline"
let attr_substitute_lid =  attr "Substitute"
let normalize_for_extraction_lid = psconst "normalize_for_extraction"
let normalize_for_extraction_type_lid = psconst "normalize_for_extraction_type"

let tcdecltime_attr = attr "tcdecltime"
let noextract_to_attr = attr "noextract_to"
let unifier_hint_injective_lid = attr "unifier_hint_injective"
let commute_nested_matches_lid = attr "commute_nested_matches"
let ite_soundness_by_attr = attr "ite_soundness_by"
let default_effect_attr = attr "default_effect"
let top_level_effect_attr = attr "top_level_effect"
let effect_parameter_attr = attr "effect_param"
let bind_has_range_args_attr = attr "bind_has_range_args"
let primitive_extraction_attr = attr "primitive_extraction"
let binder_strictly_positive_attr = attr "strictly_positive"
let binder_unused_attr = attr "unused"
let no_auto_projectors_decls_attr = attr "no_auto_projectors_decls"
let no_auto_projectors_attr = attr "no_auto_projectors"
let no_subtping_attr_lid = attr "no_subtyping"
let admit_termination_lid = attr "admit_termination"
let admitted_lid = attr "admitted"
let unrefine_binder_attr = pconst "unrefine"
let do_not_unrefine_attr = pconst "do_not_unrefine"
let desugar_of_variant_record_lid = attr "desugar_of_variant_record"
let coercion_lid = attr "coercion"

let projector_attr     = pconst "projector"
let discriminator_attr = pconst "discriminator"

let remove_unused_type_parameters_lid = psconst "remove_unused_type_parameters"


//the type of well-founded relations, used for decreases clauses with relations
let well_founded_relation_lid = p2l ["FStar"; "WellFounded"; "well_founded_relation"]

let gen_reset =
    let x = mk_ref 0 in
    let gen () = U.incr x; U.read x in
    let reset () = U.write x 0 in
    gen, reset
let next_id = fst gen_reset

let sli (l:lident) : string =
  if FStarC.Options.print_real_names()
  then string_of_lid l
  else string_of_id (ident_of_lid l)

let const_to_string x = match x with
  | Const_effect -> "Effect"
  | Const_unit -> "()"
  | Const_bool b -> if b then "true" else "false"
  | Const_real r -> r^"R"
  | Const_string(s, _) -> Format.fmt1 "\"%s\"" s
  | Const_int (x, _) -> x
  | Const_char c -> "'" ^ U.string_of_char c ^ "'"
  | Const_range r -> FStarC.Range.string_of_range r
  | Const_range_of -> "range_of"
  | Const_set_range_of -> "set_range_of"
  | Const_reify lopt ->
    Format.fmt1 "reify%s"
      (match lopt with
       | None -> ""
       | Some l -> Format.fmt1 "<%s>" (string_of_lid l))    
  | Const_reflect l -> Format.fmt1 "[[%s.reflect]]" (sli l)

let is_name (lid:lident) =
  let c = U.char_at (string_of_id (ident_of_lid lid)) 0 in
  U.is_upper c

let term_view_lid  = p2l ["FStar"; "Reflection"; "V1"; "Data"; "term_view"]

(* tactic constants *)
let fstar_tactics_lid' s : lid = FStarC.Ident.lid_of_path (["FStar"; "Tactics"]@s) FStarC.Range.dummyRange
let fstar_stubs_tactics_lid' s : lid = FStarC.Ident.lid_of_path (["FStar"; "Stubs"; "Tactics"]@s) FStarC.Range.dummyRange
let fstar_tactics_lid  s = fstar_tactics_lid' [s]
let tac_lid = fstar_tactics_lid' ["Effect"; "tac"]
let tactic_lid = fstar_tactics_lid' ["Effect"; "tactic"]

let tac_opaque_attr = pconst "tac_opaque"

let meta_projectors_attr = fstar_tactics_lid' ["MkProjectors"; "meta_projectors"]
let mk_projs_lid   = fstar_tactics_lid' ["MkProjectors"; "mk_projs"]

let mk_class_lid   = fstar_tactics_lid' ["Typeclasses"; "mk_class"]
let tcresolve_lid  = fstar_tactics_lid' ["Typeclasses"; "tcresolve"]
let tcclass_lid = fstar_tactics_lid' ["Typeclasses"; "tcclass"]
let tcinstance_lid = fstar_tactics_lid' ["Typeclasses"; "tcinstance"]
let no_method_lid = fstar_tactics_lid' ["Typeclasses"; "no_method"]

let effect_TAC_lid = fstar_tactics_lid' ["Effect"; "TAC"] // actual effect
let effect_Tac_lid = fstar_tactics_lid' ["Effect"; "Tac"] // trivial variant

let by_tactic_lid = fstar_tactics_lid' ["Effect"; "with_tactic"]
let rewrite_by_tactic_lid = fstar_tactics_lid' ["Effect"; "rewrite_with_tactic"]
let synth_lid = fstar_tactics_lid' ["Effect"; "synth_by_tactic"]
let assert_by_tactic_lid = fstar_tactics_lid' ["Effect"; "assert_by_tactic"]
let fstar_syntax_syntax_term = FStarC.Ident.lid_of_str "FStarC.Syntax.Syntax.term"
let binder_lid = lid_of_path (["FStar"; "Stubs"; "Reflection"; "Types"; "binder"]) FStarC.Range.dummyRange
let binders_lid = lid_of_path (["FStar"; "Stubs"; "Reflection"; "Types"; "binders"]) FStarC.Range.dummyRange
let bv_lid = lid_of_path (["FStar"; "Stubs"; "Reflection"; "Types"; "bv"]) FStarC.Range.dummyRange
let fv_lid = lid_of_path (["FStar"; "Stubs"; "Reflection"; "Types"; "fv"]) FStarC.Range.dummyRange
let postprocess_with = p2l ["FStar"; "Tactics"; "Effect"; "postprocess_with"]
let postprocess_type = p2l ["FStar"; "Tactics"; "Effect"; "postprocess_type"]
let preprocess_with = p2l ["FStar"; "Tactics"; "Effect"; "preprocess_with"]
let postprocess_extr_with = p2l ["FStar"; "Tactics"; "Effect"; "postprocess_for_extraction_with"]
let term_lid       = p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "term"]
let ctx_uvar_and_subst_lid = p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "ctx_uvar_and_subst"]
let universe_uvar_lid      = p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "universe_uvar"]
let check_with_lid = lid_of_path (["FStar"; "Stubs"; "VConfig"; "check_with"]) FStarC.Range.dummyRange

let decls_lid      = p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "decls"]

// meta dsl constants
let dsl_typing_builtin s = lid_of_path (["FStar"; "Reflection"; "Typing"; "Builtins"]@[s]) FStarC.Range.dummyRange
let dsl_tac_typ_lid = lid_of_path ["FStar"; "Reflection"; "Typing"; "dsl_tac_t"] FStarC.Range.dummyRange


(* Calculational proofs, from FStar.Calc *)
let calc_lid i : lid = lid_of_path ["FStar"; "Calc"; i] FStarC.Range.dummyRange
let calc_init_lid   = calc_lid "calc_init"
let calc_step_lid   = calc_lid "calc_step"
let calc_finish_lid = calc_lid "calc_finish"
let calc_push_impl_lid = calc_lid "calc_push_impl"

(* Classical proofs, from FStar.Classical *)
let classical_sugar_lid i : lid = lid_of_path ["FStar"; "Classical"; "Sugar"; i] FStarC.Range.dummyRange

let forall_intro_lid = classical_sugar_lid "forall_intro"
let exists_intro_lid = classical_sugar_lid "exists_intro"
let implies_intro_lid = classical_sugar_lid "implies_intro"
let or_intro_left_lid = classical_sugar_lid "or_intro_left"
let or_intro_right_lid = classical_sugar_lid "or_intro_right"
let and_intro_lid = classical_sugar_lid "and_intro"

let forall_elim_lid = classical_sugar_lid "forall_elim"
let exists_elim_lid = classical_sugar_lid "exists_elim"
let implies_elim_lid = classical_sugar_lid "implies_elim"
let or_elim_lid = classical_sugar_lid "or_elim"
let and_elim_lid = classical_sugar_lid "and_elim"


let match_returns_def_name = reserved_prefix ^ "_ret_"

let steel_memory_inv_lid = FStarC.Ident.lid_of_path ["Steel"; "Memory"; "inv"] FStarC.Range.dummyRange

let steel_new_invariant_lid = FStarC.Ident.lid_of_path ["Steel"; "Effect"; "Atomic"; "new_invariant"] FStarC.Range.dummyRange
let steel_st_new_invariant_lid = FStarC.Ident.lid_of_path ["Steel"; "ST"; "Util"; "new_invariant"] FStarC.Range.dummyRange

let steel_with_invariant_g_lid = FStarC.Ident.lid_of_path ["Steel"; "Effect"; "Atomic"; "with_invariant_g"] FStarC.Range.dummyRange
let steel_st_with_invariant_g_lid = FStarC.Ident.lid_of_path ["Steel"; "ST"; "Util"; "with_invariant_g"] FStarC.Range.dummyRange

let steel_with_invariant_lid = FStarC.Ident.lid_of_path ["Steel"; "Effect"; "Atomic"; "with_invariant"] FStarC.Range.dummyRange
let steel_st_with_invariant_lid = FStarC.Ident.lid_of_path ["Steel"; "ST"; "Util"; "with_invariant"] FStarC.Range.dummyRange


(* on_domain_lids are constant, so compute them once *)
let fext_lid s = Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s] FStarC.Range.dummyRange
let fext_on_domain_lid = fext_lid "on_domain"
let fext_on_dom_lid = fext_lid "on_dom"
let fext_on_domain_g_lid = fext_lid "on_domain_g"
let fext_on_dom_g_lid = fext_lid "on_dom_g"

let sealed_lid      = p2l ["FStar"; "Sealed"; "sealed"]
let seal_lid        = p2l ["FStar"; "Sealed"; "seal"]
let unseal_lid      = p2l ["FStar"; "Stubs"; "Tactics"; "Unseal"; "unseal"] (* In a separate module due to the mention of TAC *)
let map_seal_lid    = p2l ["FStar"; "Sealed"; "map_seal"]
let bind_seal_lid   = p2l ["FStar"; "Sealed"; "bind_seal"]
let tref_lid        = p2l ["FStar"; "Stubs"; "Tactics"; "Types"; "tref"]

let document_lid = p2l ["FStar"; "Pprint"; "document"]
let issue_lid = p2l ["FStar"; "Issue"; "issue"]

let extract_as_impure_effect_lid = attr "extract_as_impure_effect"
