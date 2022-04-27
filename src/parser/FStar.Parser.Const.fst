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
module FStar.Parser.Const
open FStar.String
open FStar.Compiler.Effect
open FStar.Compiler.Util
open FStar.Ident
open FStar.Compiler.Range
open FStar.Const
open FStar.Compiler.List
module U = FStar.Compiler.Util
module Options = FStar.Options
module List = FStar.Compiler.List

let p2l l = lid_of_path l dummyRange

let pconst s              = p2l ["Prims";s]
let psconst s             = p2l ["FStar"; "Pervasives"; s]
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

let salloc_lid = p2l ["FStar"; "ST"; "salloc"]
let swrite_lid = p2l ["FStar"; "ST"; "op_Colon_Equals"]
let sread_lid = p2l ["FStar"; "ST"; "op_Bang"]

let max_lid = p2l ["max"]

let real_lid  = p2l ["FStar"; "Real"; "real"]

let float_lid  = p2l ["FStar"; "Float"; "float"]

let char_lid  = p2l ["FStar"; "Char"; "char"]

let heap_lid   = p2l ["FStar"; "Heap"; "heap"]

let logical_lid = pconst "logical"

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
let dtuple2_lid     = pconst "dtuple2" // for l_Exists

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
let trivial_pure_post_lid = psconst "trivial_pure_post"
let pure_assert_wp_lid    = pconst "pure_assert_wp0"
let pure_assume_wp_lid    = pconst "pure_assume_wp0"
let assert_norm_lid       = p2l ["FStar"; "Pervasives"; "assert_norm"]
(* list_append_lid is needed to desugar @ in the compiler *)
let list_append_lid       = p2l ["FStar"; "List"; "append"]
(* list_tot_append_lid is used to desugar @ everywhere else *)
let list_tot_append_lid   = p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let id_lid                = psconst "id"

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
let string_compare = p2l ["FStar"; "String"; "compare"]
let order_lid       = p2l ["FStar"; "Order"; "order"]
let vconfig_lid     = p2l ["FStar"; "VConfig"; "vconfig"]
let mkvconfig_lid   = p2l ["FStar"; "VConfig"; "Mkvconfig"]

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

(* The "All" monad and its associated symbols *)
let compiler_effect_lid          = p2l ["FStar"; "Compiler"; "Effect"]
let compiler_effect_ALL_lid      = p2l ["FStar"; "Compiler"; "Effect"; "ALL"]
let compiler_effect_ML_lid       = p2l ["FStar"; "Compiler"; "Effect"; "ML"]
let compiler_effect_failwith_lid = p2l ["FStar"; "Compiler"; "Effect"; "failwith"]
let compiler_effect_try_with_lid = p2l ["FStar"; "Compiler"; "Effect"; "try_with"]

let all_lid          = p2l ["FStar"; "All"]
let all_ALL_lid      = p2l ["FStar"; "All"; "All"]
let all_ML_lid       = p2l ["FStar"; "All"; "ML"]
let all_failwith_lid = p2l ["FStar"; "All"; "failwith"]
let all_try_with_lid = p2l ["FStar"; "All"; "try_with"]

let effect_ALL_lid () =
  if Options.ml_ish()
  then compiler_effect_ALL_lid
  else all_lid

let effect_ML_lid () =
  if Options.ml_ish()
  then compiler_effect_ML_lid
  else all_ML_lid

let failwith_lid () =
  if Options.ml_ish()
  then compiler_effect_failwith_lid
  else all_failwith_lid

let try_with_lid () =
  if Options.ml_ish()
  then compiler_effect_try_with_lid
  else all_try_with_lid

let as_requires    = pconst "as_requires"
let as_ensures     = pconst "as_ensures"
let decreases_lid  = pconst "decreases"

let inspect        = p2l ["FStar"; "Tactics"; "Builtins"; "inspect"]
let pack           = p2l ["FStar"; "Tactics"; "Builtins"; "pack"]
let binder_to_term = p2l ["FStar"; "Tactics"; "Derived"; "binder_to_term"]

let reveal = p2l ["FStar"; "Ghost"; "reveal"]
let hide   = p2l ["FStar"; "Ghost"; "hide"]

let term_lid       = p2l ["FStar"; "Reflection"; "Types"; "term"]
let term_view_lid  = p2l ["FStar"; "Reflection"; "Data"; "term_view"]

let decls_lid      = p2l ["FStar"; "Reflection"; "Data"; "decls"]

let ctx_uvar_and_subst_lid = p2l ["FStar"; "Reflection"; "Types"; "ctx_uvar_and_subst"]


let range_lid      = pconst "range"
let range_of_lid   = pconst "range_of"
let labeled_lid    = pconst "labeled"
let range_0        = pconst "range_0"
let guard_free     = pconst "guard_free"
let inversion_lid  = p2l ["FStar"; "Pervasives"; "inversion"]
let with_type_lid  = psconst "with_type"

(* Constants for marking terms with normalization hints *)
let normalize      = psconst "normalize"
let normalize_term = psconst "normalize_term"
let norm           = psconst "norm"

(* lids for normalizer steps *)
let steps_simpl         = psconst "simplify"
let steps_weak          = psconst "weak"
let steps_hnf           = psconst "hnf"
let steps_primops       = psconst "primops"
let steps_zeta          = psconst "zeta"
let steps_zeta_full     = psconst "zeta_full"
let steps_iota          = psconst "iota"
let steps_delta         = psconst "delta"
let steps_reify         = psconst "reify_"
let steps_unfoldonly    = psconst "delta_only"
let steps_unfoldfully   = psconst "delta_fully"
let steps_unfoldattr    = psconst "delta_attr"
let steps_unfoldqual    = psconst "delta_qualifier"
let steps_nbe           = psconst "nbe"
let steps_unmeta        = psconst "unmeta"

(* attributes *)
let deprecated_attr = pconst "deprecated"
let warn_on_use_attr = pconst "warn_on_use"
let inline_let_attr = p2l ["FStar"; "Pervasives"; "inline_let"]
let rename_let_attr = p2l ["FStar"; "Pervasives"; "rename_let"]
let plugin_attr     = p2l ["FStar"; "Pervasives"; "plugin"]
let tcnorm_attr    =  p2l ["FStar"; "Pervasives"; "tcnorm"]
let dm4f_bind_range_attr = p2l ["FStar"; "Pervasives"; "dm4f_bind_range"]
let must_erase_for_extraction_attr = psconst "must_erase_for_extraction"
let strict_on_arguments_attr = p2l ["FStar"; "Pervasives"; "strict_on_arguments"]
let resolve_implicits_attr_string = "FStar.Pervasives.resolve_implicits"
let handle_smt_goals_attr = psconst "handle_smt_goals"
let handle_smt_goals_attr_string = "FStar.Pervasives.handle_smt_goals"
let erasable_attr = p2l ["FStar"; "Pervasives"; "erasable"]
let comment_attr = p2l ["FStar"; "Pervasives"; "Comment"]
let fail_attr      = psconst "expect_failure"
let fail_lax_attr  = psconst "expect_lax_failure"
let tcdecltime_attr = psconst "tcdecltime"
let noextract_to_attr = psconst "noextract_to"
let unifier_hint_injective_lid = psconst "unifier_hint_injective"
let normalize_for_extraction_lid = psconst "normalize_for_extraction"
let postprocess_with = p2l ["FStar"; "Tactics"; "Effect"; "postprocess_with"]
let preprocess_with = p2l ["FStar"; "Tactics"; "Effect"; "preprocess_with"]
let postprocess_extr_with = p2l ["FStar"; "Tactics"; "Effect"; "postprocess_for_extraction_with"]
let check_with_lid = lid_of_path (["FStar"; "Reflection"; "Builtins"; "check_with"]) FStar.Compiler.Range.dummyRange
let commute_nested_matches_lid = psconst "commute_nested_matches"
let allow_informative_binders_attr = psconst "allow_informative_binders"
let remove_unused_type_parameters_lid = psconst "remove_unused_type_parameters"
let ite_soundness_by_attr = psconst "ite_soundness_by"
let binder_strictly_positive_attr = psconst "strictly_positive"
let no_auto_projectors_attr = psconst "no_auto_projectors"


//the type of well-founded relations, used for decreases clauses with relations
let well_founded_relation_lid = p2l ["FStar"; "WellFounded"; "well_founded_relation"]

let gen_reset =
    let x = U.mk_ref 0 in
    let gen () = U.incr x; U.read x in
    let reset () = U.write x 0 in
    gen, reset
let next_id = fst gen_reset

let sli (l:lident) : string =
  if FStar.Options.print_real_names()
  then string_of_lid l
  else string_of_id (ident_of_lid l)

let const_to_string x = match x with
  | Const_effect -> "Effect"
  | Const_unit -> "()"
  | Const_bool b -> if b then "true" else "false"
  | Const_real r -> r^"R"
  | Const_float x ->      U.string_of_float x
  | Const_string(s, _) -> U.format1 "\"%s\"" s
  | Const_bytearray _  ->  "<bytearray>"
  | Const_int (x, _) -> x
  | Const_char c -> "'" ^ U.string_of_char c ^ "'"
  | Const_range r -> FStar.Compiler.Range.string_of_range r
  | Const_range_of -> "range_of"
  | Const_set_range_of -> "set_range_of"
  | Const_reify -> "reify"
  | Const_reflect l -> U.format1 "[[%s.reflect]]" (sli l)


(* Tuples  *)

let mk_tuple_lid n r =
  let t = U.format1 "tuple%s" (U.string_of_int n) in
  set_lid_range (psnconst t) r

let lid_tuple2   = mk_tuple_lid 2 dummyRange
let lid_tuple3   = mk_tuple_lid 3 dummyRange

let is_tuple_constructor_string (s:string) :bool =
  U.starts_with s "FStar.Pervasives.Native.tuple"

let is_tuple_constructor_id  id  = is_tuple_constructor_string (string_of_id id)
let is_tuple_constructor_lid lid = is_tuple_constructor_string (string_of_lid lid)

let mk_tuple_data_lid n r =
  let t = U.format1 "Mktuple%s" (U.string_of_int n) in
  set_lid_range (psnconst t) r

let lid_Mktuple2 = mk_tuple_data_lid 2 dummyRange
let lid_Mktuple3 = mk_tuple_data_lid 3 dummyRange

let is_tuple_datacon_string (s:string) :bool =
  U.starts_with s "FStar.Pervasives.Native.Mktuple"

let is_tuple_datacon_id  id  = is_tuple_datacon_string (string_of_id id)
let is_tuple_datacon_lid lid = is_tuple_datacon_string (string_of_lid lid)

let is_tuple_data_lid f n =
  lid_equals f (mk_tuple_data_lid n dummyRange)

let is_tuple_data_lid' f = is_tuple_datacon_string (string_of_lid f)


(* Dtuples *)

(* dtuple is defined in prims if n = 2, in pervasives otherwise *)
let mod_prefix_dtuple (n:int) :(string -> lident) =
  if n = 2 then pconst else psconst

let mk_dtuple_lid n r =
  let t = U.format1 "dtuple%s" (U.string_of_int n) in
  set_lid_range ((mod_prefix_dtuple n) t) r

let is_dtuple_constructor_string (s:string) :bool =
  s = "Prims.dtuple2" || U.starts_with s "FStar.Pervasives.dtuple"

let is_dtuple_constructor_lid lid = is_dtuple_constructor_string (string_of_lid lid)

let mk_dtuple_data_lid n r =
  let t = U.format1 "Mkdtuple%s" (U.string_of_int n) in
  set_lid_range ((mod_prefix_dtuple n) t) r

let is_dtuple_datacon_string (s:string) :bool =
  s = "Prims.Mkdtuple2" || U.starts_with s "FStar.Pervasives.Mkdtuple"

let is_dtuple_data_lid f n =
  lid_equals f (mk_dtuple_data_lid n dummyRange)

let is_dtuple_data_lid' f = is_dtuple_datacon_string (string_of_lid f)

let is_name (lid:lident) =
  let c = U.char_at (string_of_id (ident_of_lid lid)) 0 in
  U.is_upper c

(* tactic constants *)
let fstar_tactics_lid' s : lid = FStar.Ident.lid_of_path (["FStar"; "Tactics"]@s) FStar.Compiler.Range.dummyRange
let fstar_tactics_lid  s = fstar_tactics_lid' [s]
let tac_lid = fstar_tactics_lid' ["Effect"; "tac"]
let tactic_lid = fstar_tactics_lid' ["Effect"; "tactic"]

let mk_class_lid   = fstar_tactics_lid' ["Typeclasses"; "mk_class"]
let tcresolve_lid  = fstar_tactics_lid' ["Typeclasses"; "tcresolve"]
let tcinstance_lid = fstar_tactics_lid' ["Typeclasses"; "tcinstance"]

let effect_TAC_lid = fstar_tactics_lid' ["Effect"; "TAC"] // actual effect
let effect_Tac_lid = fstar_tactics_lid' ["Effect"; "Tac"] // trivial variant

let by_tactic_lid = fstar_tactics_lid' ["Effect"; "with_tactic"]
let rewrite_by_tactic_lid = fstar_tactics_lid' ["Effect"; "rewrite_with_tactic"]
let synth_lid = fstar_tactics_lid' ["Effect"; "synth_by_tactic"]
let assert_by_tactic_lid = fstar_tactics_lid' ["Effect"; "assert_by_tactic"]
let fstar_syntax_syntax_term = FStar.Ident.lid_of_str "FStar.Syntax.Syntax.term"
let binder_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "binder"]) FStar.Compiler.Range.dummyRange
let binders_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "binders"]) FStar.Compiler.Range.dummyRange
let bv_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "bv"]) FStar.Compiler.Range.dummyRange
let fv_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "fv"]) FStar.Compiler.Range.dummyRange
let norm_step_lid = psconst "norm_step"

(* Calculational proofs, from FStar.Calc *)
let calc_lid i : lid = lid_of_path ["FStar"; "Calc"; i] FStar.Compiler.Range.dummyRange
let calc_init_lid   = calc_lid "calc_init"
let calc_step_lid   = calc_lid "calc_step"
let calc_finish_lid = calc_lid "calc_finish"
let calc_push_impl_lid = calc_lid "calc_push_impl"

(* Classical proofs, from FStar.Classical *)
let classical_sugar_lid i : lid = lid_of_path ["FStar"; "Classical"; "Sugar"; i] FStar.Compiler.Range.dummyRange

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
