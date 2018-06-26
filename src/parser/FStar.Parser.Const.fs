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
#light "off"
module FStar.Parser.Const
open FStar.ST
open FStar.All
open FStar.Util
open FStar.Ident
open FStar.Range
open FStar.Const
open FStar.List
module U = FStar.Util

let p2l l = lid_of_path l dummyRange

let pconst s              = p2l ["Prims";s]
let psconst s             = p2l ["FStar"; "Pervasives"; s]
let psnconst s            = p2l ["FStar"; "Pervasives" ; "Native" ; s]
let prims_lid             = p2l ["Prims"]
let pervasives_native_lid = p2l ["FStar"; "Pervasives"; "Native"]
let pervasives_lid        = p2l ["FStar"; "Pervasives"]
let fstar_ns_lid          = p2l ["FStar"]

(* Primitive types *)
let bool_lid        = pconst "bool"
let unit_lid        = pconst "unit"
let squash_lid      = pconst "squash"
let auto_squash_lid = pconst "auto_squash"
let string_lid      = pconst "string"
let bytes_lid       = pconst "bytes"
let int_lid         = pconst "int"
let exn_lid         = pconst "exn"
let list_lid        = pconst "list"
let option_lid      = psnconst "option"
let either_lid      = psconst "either"
let pattern_lid     = pconst "pattern"
let precedes_lid    = pconst "precedes"
let lex_t_lid       = pconst "lex_t"
let lexcons_lid     = pconst "LexCons"
let lextop_lid      = pconst "LexTop"
let smtpat_lid      = pconst "smt_pat"
let smtpatOr_lid    = pconst "smt_pat_or"
let monadic_lid     = pconst "M"
let spinoff_lid     = pconst "spinoff"

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

let float_lid  = p2l ["FStar"; "Float"; "float"]

let char_lid  = p2l ["FStar"; "Char"; "char"]

let heap_lid   = p2l ["FStar"; "Heap"; "heap"]

let logical_lid = pconst "logical"

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
let c_true_lid   = pconst "c_True"
let c_false_lid  = pconst "c_False"
let c_and_lid    = pconst "c_and"
let c_or_lid     = pconst "c_or"
let dtuple2_lid  = pconst "dtuple2" // for l_Exists

(* Various equality predicates *)
let eq2_lid    = pconst  "eq2"
let eq3_lid    = pconst  "eq3"
let c_eq2_lid  = pconst "equals"
let c_eq3_lid  = pconst "h_equals"

(* Some common term constructors *)
let cons_lid        = pconst  "Cons"
let nil_lid         = pconst  "Nil"
let some_lid        = psnconst  "Some"
let none_lid        = psnconst  "None"
let assume_lid      = pconst  "_assume"
let assert_lid      = pconst  "_assert"
(* list_append_lid is needed to desugar @ in the compiler *)
let list_append_lid = p2l ["FStar"; "List"; "append"]
(* list_tot_append_lid is used to desugar @ everywhere else *)
let list_tot_append_lid = p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let strcat_lid      = p2l ["Prims"; "strcat"]
let strcat_lid'     = p2l ["FStar"; "String"; "strcat"]
let str_make_lid    = p2l ["FStar"; "String"; "make"]
let let_in_typ      = p2l ["Prims"; "Let"]
let string_of_int_lid = p2l ["Prims"; "string_of_int"]
let string_of_bool_lid = p2l ["Prims"; "string_of_bool"]
let string_compare = p2l ["FStar"; "String"; "compare"]
let order_lid       = p2l ["FStar"; "Order"; "order"]

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
let array_mk_array_lid = p2l ["FStar"; "Array"; "mk_array"]

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
let effect_Lemma_lid = pconst "Lemma"
let effect_GTot_lid  = pconst "GTot"
let effect_GHOST_lid = pconst "GHOST"
let effect_Ghost_lid = pconst "Ghost"
let effect_DIV_lid   = psconst "DIV"
let effect_Div_lid   = psconst "Div"
let effect_Dv_lid    = psconst "Dv"

(* The "All" monad and its associated symbols *)
let all_lid          = p2l ["FStar"; "All"]
let effect_ALL_lid   = p2l ["FStar"; "All"; "ALL"]
let effect_ML_lid    = p2l ["FStar"; "All"; "ML"]
let failwith_lid     = p2l ["FStar"; "All"; "failwith"]
let pipe_right_lid   = p2l ["FStar"; "All"; "pipe_right"]
let pipe_left_lid    = p2l ["FStar"; "All"; "pipe_left"]
let try_with_lid     = p2l ["FStar"; "All"; "try_with"]

let as_requires    = pconst "as_requires"
let as_ensures     = pconst "as_ensures"
let decreases_lid  = pconst "decreases"

let term_lid       = p2l ["FStar"; "Reflection"; "Types"; "term"]
let decls_lid      = p2l ["FStar"; "Reflection"; "Data"; "decls"]

let ctx_uvar_and_subst_lid = p2l ["FStar"; "Reflection"; "Types"; "ctx_uvar_and_subst"]


let range_lid      = pconst "range"
let range_of_lid   = pconst "range_of"
let labeled_lid    = pconst "labeled"
let range_0        = pconst "range_0"
let guard_free     = pconst "guard_free"
let inversion_lid  = p2l ["FStar"; "Pervasives"; "inversion"]
let with_type_lid  = psnconst "with_type"

(* Constants for marking terms with normalization hints *)
let normalize      = psnconst "normalize"
let normalize_term = psnconst "normalize_term"
let norm           = psnconst "norm"

(* lids for normalizer steps *)
let steps_simpl         = psnconst "simplify"
let steps_weak          = psnconst "weak"
let steps_hnf           = psnconst "hnf"
let steps_primops       = psnconst "primops"
let steps_zeta          = psnconst "zeta"
let steps_iota          = psnconst "iota"
let steps_delta         = psnconst "delta"
let steps_reify         = psnconst "reify_"
let steps_unfoldonly    = psnconst "delta_only"
let steps_unfoldfully   = psnconst "delta_fully"
let steps_unfoldattr    = psnconst "delta_attr"
let steps_nbe           = psnconst "nbe"

(* attributes *)
let deprecated_attr = p2l ["FStar"; "Pervasives"; "deprecated"]
let inline_let_attr = p2l ["FStar"; "Pervasives"; "inline_let"]
let plugin_attr     = p2l ["FStar"; "Pervasives"; "plugin"]
let dm4f_bind_range_attr = p2l ["FStar"; "Pervasives"; "dm4f_bind_range"]
let must_erase_for_extraction_attr = psconst "must_erase_for_extraction"
let fail_attr      = psconst "fail"
let fail_lax_attr  = psconst "fail_lax"
let assume_strictly_positive_attr_lid = p2l ["FStar"; "Pervasives"; "assume_strictly_positive"]

let gen_reset =
    let x = U.mk_ref 0 in
    let gen () = U.incr x; U.read x in
    let reset () = U.write x 0 in
    gen, reset
let next_id = fst gen_reset

let sli (l:lident) : string =
  if FStar.Options.print_real_names()
  then l.str
  else l.ident.idText

let const_to_string x = match x with
  | Const_effect -> "Effect"
  | Const_unit -> "()"
  | Const_bool b -> if b then "true" else "false"
  | Const_float x ->      U.string_of_float x
  | Const_string(s, _) -> U.format1 "\"%s\"" s
  | Const_bytearray _  ->  "<bytearray>"
  | Const_int (x, _) -> x
  | Const_char c -> "'" ^ U.string_of_char c ^ "'"
  | Const_range r -> FStar.Range.string_of_range r
  | Const_range_of -> "range_of"
  | Const_set_range_of -> "set_range_of"
  | Const_reify -> "reify"
  | Const_reflect l -> U.format1 "[[%s.reflect]]" (sli l)


(* Tuples  *)

let mk_tuple_lid n r =
  let t = U.format1 "tuple%s" (U.string_of_int n) in
  set_lid_range (psnconst t) r

let lid_tuple2   = mk_tuple_lid 2 dummyRange

let is_tuple_constructor_string (s:string) :bool =
  U.starts_with s "FStar.Pervasives.Native.tuple"

let is_tuple_constructor_lid lid = is_tuple_constructor_string (text_of_id lid)

let mk_tuple_data_lid n r =
  let t = U.format1 "Mktuple%s" (U.string_of_int n) in
  set_lid_range (psnconst t) r

let lid_Mktuple2 = mk_tuple_data_lid 2 dummyRange

let is_tuple_datacon_string (s:string) :bool =
  U.starts_with s "FStar.Pervasives.Native.Mktuple"

let is_tuple_data_lid f n =
  lid_equals f (mk_tuple_data_lid n dummyRange)

let is_tuple_data_lid' f = is_tuple_datacon_string f.str


(* Dtuples *)

(* dtuple is defined in prims if n = 2, in pervasives otherwise *)
let mod_prefix_dtuple (n:int) :(string -> lident) =
  if n = 2 then pconst else psconst

let mk_dtuple_lid n r =
  let t = U.format1 "dtuple%s" (U.string_of_int n) in
  set_lid_range ((mod_prefix_dtuple n) t) r

let is_dtuple_constructor_string (s:string) :bool =
  s = "Prims.dtuple2" || U.starts_with s "FStar.Pervasives.dtuple"

let is_dtuple_constructor_lid lid = is_dtuple_constructor_string lid.str

let mk_dtuple_data_lid n r =
  let t = U.format1 "Mkdtuple%s" (U.string_of_int n) in
  set_lid_range ((mod_prefix_dtuple n) t) r

let is_dtuple_datacon_string (s:string) :bool =
  s = "Prims.Mkdtuple2" || U.starts_with s "FStar.Pervasives.Mkdtuple"

let is_dtuple_data_lid f n =
  lid_equals f (mk_dtuple_data_lid n dummyRange)

let is_dtuple_data_lid' f = is_dtuple_datacon_string (text_of_lid f)

let is_name (lid:lident) =
  let c = U.char_at lid.ident.idText 0 in
  U.is_upper c

(* tactic constants *)
let fstar_tactics_lid' s : lid = FStar.Ident.lid_of_path (["FStar"; "Tactics"]@s) FStar.Range.dummyRange
let fstar_tactics_lid  s = fstar_tactics_lid' [s]
let tactic_lid = fstar_tactics_lid' ["Effect"; "tactic"]
let u_tac_lid = fstar_tactics_lid' ["Effect"; "__tac"]

let tcresolve_lid  = fstar_tactics_lid' ["Typeclasses"; "tcresolve"]
let tcnorm_lid     = fstar_tactics_lid' ["Typeclasses"; "tcnorm"]
let tcinstance_lid = fstar_tactics_lid' ["Typeclasses"; "instance"]

let effect_TAC_lid = fstar_tactics_lid' ["Effect"; "TAC"] // actual effect
let effect_Tac_lid = fstar_tactics_lid' ["Effect"; "Tac"] // trivial variant

let by_tactic_lid = fstar_tactics_lid' ["Effect"; "__by_tactic"]
let synth_lid = fstar_tactics_lid' ["Effect"; "synth_by_tactic"]
let assert_by_tactic_lid = fstar_tactics_lid' ["Effect"; "assert_by_tactic"]
let reify_tactic_lid = fstar_tactics_lid' ["Effect"; "reify_tactic"]
let fstar_syntax_syntax_term = FStar.Ident.lid_of_str "FStar.Syntax.Syntax.term"
let binder_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "binder"]) FStar.Range.dummyRange
let binders_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "binders"]) FStar.Range.dummyRange
let bv_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "bv"]) FStar.Range.dummyRange
let fv_lid = lid_of_path (["FStar"; "Reflection"; "Types"; "fv"]) FStar.Range.dummyRange
let norm_step_lid = lid_of_path (["FStar"; "Syntax"; "Embeddings"; "norm_step"]) FStar.Range.dummyRange
