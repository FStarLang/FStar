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
module FStar.Absyn.Const
open FStar.Absyn.Syntax
open FStar.Util

let p2l l = lid_of_path l dummyRange
let pconst s     = p2l ["Prims";s]
let prims_lid    = p2l ["Prims"]
let fstar_ns_lid = p2l ["FStar"]

(* Primitive types *)
let bool_lid   = pconst  "bool"
let unit_lid   = pconst  "unit"
let string_lid = pconst  "string"
let bytes_lid  = pconst  "bytes"
let char_lid   = pconst  "char"
let int_lid    = pconst  "int"
let uint8_lid  = pconst  "uint8"
let int64_lid  = pconst  "int64"
let float_lid  = pconst  "float"
let exn_lid    = pconst  "exn"
let list_lid   = pconst  "list"
let pattern_lid = pconst "pattern"
let precedes_lid = pconst "Precedes"
let lex_t_lid    = pconst "lex_t"
let lexcons_lid  = pconst "LexCons"
let lextop_lid   = pconst "LexTop"
let smtpat_lid   = pconst "SMTPat"
let smtpatT_lid  = pconst "SMTPatT"
let smtpatOr_lid = pconst "SMTPatOr"

let int32_lid  = p2l ["FStar"; "Int32"; "int32"]
let int31_lid  = p2l ["FStar"; "Int31"; "int31"]
let heap_lid   = p2l ["FStar"; "Heap"; "heap"]

(* Logical connectives and operators *)
let kunary k k'              = mk_Kind_arrow([null_t_binder k], k') dummyRange
let kbin k1 k2 k'            = mk_Kind_arrow([null_t_binder k1; null_t_binder k2], k') dummyRange
let ktern k1 k2 k3 k'        = mk_Kind_arrow([null_t_binder k1;
                                              null_t_binder k2;
                                              null_t_binder k3], k') dummyRange
let true_lid   = pconst "True"
let false_lid  = pconst "False"
let and_lid    = pconst "l_and"
let or_lid     = pconst "l_or"
let not_lid    = pconst "l_not"
let imp_lid    = pconst "l_imp"
let iff_lid    = pconst "l_iff"
let ite_lid    = pconst "ITE"
let exists_lid = pconst "Exists"
let forall_lid = pconst "Forall"
let exTyp_lid  = pconst "ExistsTyp"
let allTyp_lid = pconst "ForallTyp"
let b2t_lid    = pconst "b2t" (* coercion from boolean to type *)
let using_IH   = pconst "InductionHyp"
let using_lem  = pconst "Using"
let admit_lid  = pconst "admit"
let magic_lid  = pconst "magic"

(* Various equality predicates *)
let eq_lid     = pconst  "Eq"
let eq2_lid    = pconst  "Eq2"
let eqA_lid    = pconst  "EqA"
let eqT_lid    = pconst  "EqTyp"
let neq_lid    = pconst  "neq"
let neq2_lid   = pconst  "neq2"

(* Some common term constructors *)
let exp_true_bool   = mk_Exp_constant (Const_bool true) None dummyRange
let exp_false_bool  = mk_Exp_constant (Const_bool false) None dummyRange
let exp_unit        = mk_Exp_constant (Const_unit) None dummyRange
let cons_lid        = pconst  "Cons"
let nil_lid         = pconst  "Nil"
let assume_lid      = pconst  "_assume"
let assert_lid      = pconst  "_assert"
let list_append_lid = p2l ["FStar"; "List"; "append"]
let strcat_lid      = p2l ["Prims"; "strcat"]
let let_in_typ      = p2l ["Prims"; "Let"]

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
let set_lid       = p2l ["FStar"; "Set"]
let set_empty     = p2l ["FStar"; "Set"; "empty"]
let set_singleton = p2l ["FStar"; "Set"; "singleton"]
let set_union     = p2l ["FStar"; "Set"; "union"]

(* monad constants *)
let effect_PURE_lid  = pconst "PURE"
let effect_Pure_lid  = pconst "Pure"
let effect_Tot_lid   = pconst "Tot"
let effect_Lemma_lid = pconst "Lemma"
let effect_GTot_lid  = pconst "GTot"
let effect_GHOST_lid = pconst "GHOST"
let effect_Ghost_lid = pconst "Ghost"

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

