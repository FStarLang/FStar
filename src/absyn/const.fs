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

let p2l l = lid_of_path l dummyRange 
let pconst s  = p2l ["Prims";s]
let prims_lid = p2l ["Prims"]

(* Primitive types *)
let extern_id = p2l ["extern"]
let heap_lid     = pconst  "heap" 
let bool_lid     = pconst  "bool" 
let unit_lid     = pconst  "unit" 
let string_lid   = pconst  "string" 
let bytes_lid   = pconst  "bytes" 
let int_lid = pconst  "int" 
let num_lid = pconst  "number" 
let float_lid = pconst  "float" 
let exn_lid = pconst  "exn" 

(* Logical connectives and operators *)
let kun k k'                 = Kind_tcon(None, k, k')
let kbin k k'                = Kind_tcon(None, k, Kind_tcon(None, k, k')) 
let ktern k k'               = Kind_tcon(None, k, Kind_tcon(None, k, Kind_tcon(None, k, k')))
let true_lid = pconst "True"
let false_lid = pconst "False"
let and_lid = pconst "l_and"  
let or_lid = pconst "l_or"    
let not_lid = pconst "l_not"  
let lbl_lid = pconst "LBL"    
let implies_lid = pconst "l_implies"
let iff_lid = pconst "l_iff"      
let ite_lid = pconst "IfThenElse" 
let exists_lid = pconst "Exists"  
let forall_lid = pconst "Forall"  
let exTyp_lid = pconst "ExistsTyp"
let allTyp_lid = pconst "ForallTyp"

(* Predicates corresponding to binops *)
let lt_lid    = pconst  "LT"
let gt_lid    = pconst  "GT"
let lte_lid   = pconst  "LTE"
let gte_lid   = pconst  "GTE"
let eq_lid    = pconst  "Eq"
let eq2_lid   = pconst  "Eq2"
let eqA_lid   = pconst  "EqA"
let eqTyp_lid = pconst  "EqTyp"
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
let exp_true_bool  = withsort (Exp_constant (Const_bool true)) Typ_unknown
let exp_false_bool = withsort (Exp_constant (Const_bool false)) Typ_unknown
let cons_lid       = pconst  "Cons"
let nil_lid        = pconst  "Nil"
let ref_lid        = pconst  "ref"
let assume_lid     = pconst  "Assume"
let assert_lid     = pconst  "Assert"
let pipe_right_lid    = pconst "pipe_right"
let pipe_left_lid     = pconst "pipe_left"
let list_append_lid   = p2l ["List"; "append"]
let string_concat_lid = p2l ["String"; "concat"]

(* Primitive operators *)
let op_Eq              = pconst "op_Equality"
let op_notEq           = pconst "op_disEquality"
let op_ColonEq         = pconst "_dummy_op_ColonEquals"
let op_And_lid         = pconst "_dummy_op_AmpAmp"
let op_Or_lid          = pconst "_dummy_op_BarBar"
let op_Not_lid         = pconst "_dummy_op_Negation"
let op_Add_lid         = pconst "_dummy_op_Addition"
let op_Subtraction_lid = pconst "_dummy_op_Subtraction"
let op_Multiply_lid    = pconst "_dummy_op_Multiply"
let op_Division_lid    = pconst "_dummy_op_Division"
let op_Modulus_lid     = pconst "_dummy_op_Modulus"
let op_lte_lid         = pconst "_dummy_op_LessThanOrEqual"
let op_gte_lid         = pconst "_dummy_op_GreaterThanOrEqual"
let op_lt_lid          = pconst "_dummy_op_LessThan"
let op_gt_lid          = pconst "_dummy_op_GreatherThan"


let op_LT              = p2l ["op_LessThan"]
let op_LTE             = p2l ["op_LessThanOrEqual"]
let op_GT              = p2l ["op_GreaterThan"]
let op_GTE             = p2l ["op_GreaterThanOrEqual"]
let op_Subtraction     = p2l ["op_Subtraction"]
let op_Minus           = p2l ["op_Minus"]
let op_Addition        = p2l ["op_Addition"]
let op_Multiply        = p2l ["op_Multiply"]
let op_Division        = p2l ["op_Division"]
let op_Modulus         = p2l ["op_Modulus"]
let op_And             = p2l ["op_AmpAmp"]
let op_Or              = p2l ["op_BarBar"]

(* control primitives *)
let try_with_lid       = p2l ["try_with"]

(* Array constants *)
let array_lid          = p2l ["Array"; "array"]
let array_mk_array_lid = p2l ["Array"; "mk_array"]

(* Dijkstra monad constants *)
let dst_lid      = p2l ["DST"; "DST"]
let returnTX_lid = p2l ["DST"; "returnTX"]
let bindTX_lid   = p2l ["DST"; "bindTX"]
let write_lid    = p2l ["DST"; "write"]
let read_lid     = p2l ["DST"; "read"]

(* relational mode constants *)
let lproj_lid            = pconst  "L"
let rproj_lid            = pconst  "R"
let reln_lid             = pconst  "Relational" 
let doublesided_lid      = pconst  "DoubleSided"  
let composeClassic_lid   = pconst  "composeClassic"
