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
module FStar.Syntax.Const
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Ident
open FStar.Range
open FStar.Const

let mk t : term = mk t None dummyRange
let p2l l = lid_of_path l dummyRange
let pconst s       = p2l ["Prims";s]
let psconst s      = p2l ["FStar"; "Pervasives"; s]
let prims_lid      = p2l ["Prims"]
let pervasives_lid = p2l ["FStar"; "Pervasives"]
let fstar_ns_lid   = p2l ["FStar"]

(* Primitive types *)
let bool_lid     = pconst "bool"
let unit_lid     = pconst "unit"
let squash_lid   = pconst "squash"
let string_lid   = pconst "string"
let bytes_lid    = pconst "bytes"
let int_lid      = pconst "int"
let exn_lid      = pconst "exn"
let list_lid     = pconst "list"
let option_lid   = psconst "option"
let either_lid   = psconst "either"
let pattern_lid  = pconst "pattern"
let precedes_lid = pconst "precedes"
let lex_t_lid    = pconst "lex_t"
let lexcons_lid  = pconst "LexCons"
let lextop_lid   = pconst "LexTop"
let smtpat_lid   = pconst "SMTPat"
let smtpatT_lid  = pconst "SMTPatT"
let smtpatOr_lid = pconst "SMTPatOr"
let monadic_lid  = pconst "M"

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

(* Logical connectives and operators *)
let kunary k k'              = mk (Tm_arrow([null_binder k], mk_Total k'))
let kbin k1 k2 k'            = mk (Tm_arrow([null_binder k1; null_binder k2], mk_Total k'))
let ktern k1 k2 k3 k'        = mk (Tm_arrow([null_binder k1;
                                             null_binder k2;
                                             null_binder k3], mk_Total k'))
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

(* Various equality predicates *)
let eq2_lid    = pconst  "eq2"
let eq3_lid    = pconst  "eq3"

(* Some common term constructors *)
let exp_true_bool   = mk (Tm_constant (Const_bool true))
let exp_false_bool  = mk (Tm_constant (Const_bool false))
let exp_unit        = mk (Tm_constant (Const_unit))
let exp_int s       = mk (Tm_constant (Const_int (s,None))) // Makes an (unbounded) integer from its string repr.
let exp_string s    = mk (Tm_constant (Const_string (unicode_of_string s, dummyRange)))
let cons_lid        = pconst  "Cons"
let nil_lid         = pconst  "Nil"
let some_lid        = psconst  "Some"
let none_lid        = psconst  "None"
let assume_lid      = pconst  "_assume"
let assert_lid      = pconst  "_assert"
(* list_append_lid is needed to desugar @ in the compiler *)
let list_append_lid = p2l ["FStar"; "List"; "append"]
(* list_tot_append_lid is used to desugar @ everywhere else *)
let list_tot_append_lid = p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let strcat_lid      = p2l ["Prims"; "strcat"]
let let_in_typ      = p2l ["Prims"; "Let"]
let string_of_int_lid = p2l ["Prims"; "string_of_int"]
let string_of_bool_lid = p2l ["Prims"; "string_of_bool"]

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
let ref_lid       = p2l ["FStar"; "Heap"; "ref"]
let heap_ref      = p2l ["FStar"; "Heap"; "Ref"]
let set_empty     = p2l ["FStar"; "Set"; "empty"]
let set_singleton = p2l ["FStar"; "Set"; "singleton"]
let set_union     = p2l ["FStar"; "Set"; "union"]
let fstar_hyperheap_lid = p2l ["FStar"; "HyperHeap"]
let rref_lid      = p2l ["FStar"; "HyperHeap"; "rref"]
let tset_empty     = p2l ["FStar"; "TSet"; "empty"]
let tset_singleton = p2l ["FStar"; "TSet"; "singleton"]
let tset_union     = p2l ["FStar"; "TSet"; "union"]

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
let effect_DIV_lid   = pconst "DIV"

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

let range_lid      = pconst "range"
let range_of_lid   = pconst "range_of"
let labeled_lid    = pconst "labeled"
let range_0        = pconst "range_0"
let guard_free     = pconst "guard_free"

(* Constants for marking terms with normalization hints *)
let normalize      = pconst "normalize"
let normalize_term = pconst "normalize_term"

(* tactic constants *)
let fstar_tactics_lid s = FStar.Ident.lid_of_path (["FStar"; "Tactics"]@[s]) FStar.Range.dummyRange
let tactic_lid = fstar_tactics_lid "tactic"
let by_tactic_lid = fstar_tactics_lid "by_tactic"
let reify_tactic_lid = fstar_tactics_lid "reify_tactic"
let fstar_tactics_embed_lid = fstar_tactics_lid "__embed"
