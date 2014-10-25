(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module Microsoft.FStar.Absyn.Const
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Util

let p2l l = lid_of_path l dummyRange 
let pconst s  = p2l ["Prims";s]
let prims_lid = p2l ["Prims"]

(* Primitive types *)
let heap_lid   = pconst  "heap" 
let bool_lid   = pconst  "bool" 
let unit_lid   = pconst  "unit" 
let string_lid = pconst  "string" 
let bytes_lid  = pconst  "bytes" 
let char_lid   = pconst  "char" 
let int_lid    = pconst  "int" 
let uint8_lid  = pconst  "uint8" 
let int64_lid  = pconst  "int64" 
let num_lid    = pconst  "number" 
let float_lid  = pconst  "float" 
let exn_lid    = pconst  "exn" 
let precedes_lid = pconst "Precedes"
let lexpair_lid  = pconst "LexPair"
let lextop_lid   = pconst "LexTop"

(* Logical connectives and operators *)
let kunary k k'              = mk_Kind_arrow([Inl <| null_bvar k, false], k') dummyRange
let kbin k1 k2 k'            = mk_Kind_arrow([Inl <| null_bvar k1, false; 
                                              Inl <| null_bvar k2, false], k') dummyRange
let ktern k1 k2 k3 k'        = mk_Kind_arrow([Inl <| null_bvar k1, false; 
                                              Inl <| null_bvar k2, false;
                                              Inl <| null_bvar k3, false], k') dummyRange
let true_lid = pconst "True"
let false_lid = pconst "False"
let and_lid = pconst "l_and"  
let or_lid = pconst "l_or"    
let not_lid = pconst "l_not"  
let lbl_lid = pconst "LBL"    
let imp_lid = pconst "l_imp"
let iff_lid = pconst "l_iff"      
let ite_lid = pconst "ITE" 
let exists_lid = pconst "Exists"  
let forall_lid = pconst "Forall"  
let exTyp_lid  = pconst "ExistsTyp"
let allTyp_lid = pconst "ForallTyp"
let b2t_lid = pconst "b2t" (* coercion from boolean to type *)

(* Predicates corresponding to binops *)
let lt_lid    = pconst  "LT"
let gt_lid    = pconst  "GT"
let lte_lid   = pconst  "LTE"
let gte_lid   = pconst  "GTE"
let eq_lid    = pconst  "Eq"
let eq2_lid   = pconst  "Eq2"
let eqA_lid   = pconst  "EqA"
let eqT_lid   = pconst  "EqTyp"
let neq_lid   = pconst  "neq"
let neq2_lid  = pconst  "neq2"

(* Common logical functions for various theories *)
let typeof_lid = pconst "TypeOf" 
let kindof_lid = pconst "KindOf" 
let add_lid    = pconst  "Add"
let sub_lid    = pconst  "Sub"
let mul_lid    = pconst  "Mul"
let div_lid    = pconst  "Div"
let minus_lid  = pconst  "Minus"
let modulo_lid = pconst  "Modulo"

(* Some common term constructors *)
let exp_true_bool  = mk_Exp_constant (Const_bool true) tun dummyRange
let exp_false_bool = mk_Exp_constant (Const_bool false) tun dummyRange
let exp_unit       = mk_Exp_constant (Const_unit) tun dummyRange
let cons_lid       = pconst  "Cons"
let nil_lid        = pconst  "Nil"
let ref_lid        = pconst  "ref"
let assume_lid     = pconst  "Assume"
let assert_lid     = pconst  "Assert"
let pipe_right_lid    = pconst "pipe_right"
let pipe_left_lid     = pconst "pipe_left"
let list_append_lid   = p2l ["List"; "append"]
let strcat_lid = p2l ["String"; "strcat"]

(* Primitive operators *)
let op_Eq              = pconst "op_Equality"
let op_notEq           = pconst "op_disEquality"
let op_ColonEq         = pconst "op_ColonEquals"
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
let print_lid          = pconst "print"

(* control primitives *)
let try_with_lid       = pconst "try_with"

(* Array constants *)
let array_lid          = p2l ["Array"; "array"]
let array_mk_array_lid = p2l ["Array"; "mk_array"]

(* Stateful constants *)
let write_lid    = p2l ["ST"; "write"]
let read_lid     = p2l ["ST"; "read"]
let alloc_lid    = p2l ["ST"; "alloc"]

(* monad constants *)
let pure_effect_lid = pconst "PURE"
let tot_effect_lid  = p2l ["Prims";"PURE";"Tot"]
let pure_ret_lid    = p2l ["Prims";"PURE";"return"]
let pure_bind_lid   = p2l ["Prims";"PURE";"bind"]
let all_effect_lid  = pconst "ALL"
let all_ret_lid     = p2l ["Prims";"ALL";"return"]
let all_bind_lid    = p2l ["Prims";"ALL";"bind"]
let ml_effect_lid   = p2l ["Prims"; "ALL"; "ML"]
let assert_pure_lid = p2l ["Prims"; "assert_pure"]
let assume_pure_lid = p2l ["Prims"; "assume_pure"]

(* relational mode constants *)
let lproj_lid            = pconst  "L"
let rproj_lid            = pconst  "R"
let reln_lid             = pconst  "Relational" 
let doublesided_lid      = pconst  "DoubleSided"  
let composeClassic_lid   = pconst  "composeClassic"
