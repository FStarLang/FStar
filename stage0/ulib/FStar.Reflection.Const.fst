(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Reflection.Const

(* Common lids *)

// TODO: these are awful names
// TODO: _qn vs _lid

let imp_qn       = ["Prims"; "l_imp"]
let and_qn       = ["Prims"; "l_and"]
let or_qn        = ["Prims"; "l_or"]
let not_qn       = ["Prims"; "l_not"]
let iff_qn       = ["Prims"; "l_iff"]
let eq2_qn       = ["Prims"; "eq2"]
let eq1_qn       = ["Prims"; "eq"]
let true_qn      = ["Prims"; "l_True"]
let false_qn     = ["Prims"; "l_False"]
let b2t_qn       = ["Prims"; "b2t"]
let forall_qn    = ["Prims"; "l_Forall"]
let exists_qn    = ["Prims"; "l_Exists"]
let squash_qn    = ["Prims"; "squash"]
let prop_qn      = ["Prims"; "prop"]

let bool_true_qn  = ["Prims"; "true"]
let bool_false_qn = ["Prims"; "false"]

let int_lid      = ["Prims"; "int"]
let bool_lid     = ["Prims"; "bool"]
let unit_lid     = ["Prims"; "unit"]
let string_lid   = ["Prims"; "string"]

let add_qn       = ["Prims"; "op_Addition"]
let neg_qn       = ["Prims"; "op_Minus"]
let minus_qn     = ["Prims"; "op_Subtraction"]
let mult_qn      = ["Prims"; "op_Multiply"]
let mult'_qn     = ["FStar"; "Mul"; "op_Star"]
let div_qn       = ["Prims"; "op_Division"]
let lt_qn        = ["Prims"; "op_LessThan"]
let lte_qn       = ["Prims"; "op_LessThanOrEqual"]
let gt_qn        = ["Prims"; "op_GreaterThan"]
let gte_qn       = ["Prims"; "op_GreaterThanOrEqual"]
let mod_qn       = ["Prims"; "op_Modulus"]

let nil_qn       = ["Prims"; "Nil"]
let cons_qn      = ["Prims"; "Cons"]

let mktuple2_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple2"]
let mktuple3_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple3"]
let mktuple4_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple4"]
let mktuple5_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple5"]
let mktuple6_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple6"]
let mktuple7_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple7"]
let mktuple8_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple8"]

let land_qn    = ["FStar" ; "UInt" ; "logand"]
let lxor_qn    = ["FStar" ; "UInt" ; "logxor"]
let lor_qn     = ["FStar" ; "UInt" ; "logor"]
let ladd_qn    = ["FStar" ; "UInt" ; "add_mod"]
let lsub_qn    = ["FStar" ; "UInt" ; "sub_mod"]
let shiftl_qn  = ["FStar" ; "UInt" ; "shift_left"]
let shiftr_qn  = ["FStar" ; "UInt" ; "shift_right"]
let udiv_qn    = ["FStar" ; "UInt" ; "udiv"]
let umod_qn    = ["FStar" ; "UInt" ; "mod"]
let mul_mod_qn = ["FStar" ; "UInt" ; "mul_mod"]
let nat_bv_qn  = ["FStar" ; "BV"   ; "int2bv"]
