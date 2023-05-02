(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes
*)

(* Sanity tests for Printable by type. *)

module TestPrintable
open FStar.Tactics
open FStar.Seq

open FStar.Printable 

open FStar.Seq.Base
module Seq = FStar.Seq.Base

(* Sequences are abstract in their interface new val seq (a : Type u#a) : Type u#a
  so you can't test by 'proof' e.g., normalization. *)
[@@ expect_failure [19]]
let printable_seq_test_empty =  assert(to_string (empty <: seq int) = "<>") by 
 compute()


[@@ expect_failure [19]]
let printable_seq_test_one =  assert(to_string ((fun (s : seq int) -> s) (seq_of_list [1])) = "<1>") by compute()

[@@ expect_failure [19]]
let printable_seq_test_two =  assert(to_string ((fun (s : seq int) -> s) (seq_of_list [1;2])) = "<1; 2>") by compute()

(* These are a copacetic. *)
let printable_string_test1     = assert(to_string "1" == "\"1\"") by compute()
let printable_unit_test = assert(to_string () = "()") by compute()
let printable_int_test_0 = assert(to_string 0 = "0") by compute()
let printable_int_test_minus_1_let = assert(let mone = -1 in (to_string mone) = "-1") by compute()
let printable_nat_test =  assert(let v : nat = 0 in to_string v = "0") by compute()

let printable_list_test_empty = assert(let il : list nat = [] in to_string il = "[]") by compute()
let printable_list_test_one   = assert(let il : list nat = [1] in to_string il = "[1]") by compute()

let printable_list_test_two   = assert(let il : list nat = [1;2] in to_string il = "[1; 2]") by compute()
let printable_ref_test        = assert(let int_to_int42 (i: int{i=42}) = i in to_string (int_to_int42 42) = "42") by compute()

let printable_option_test_none =  assert(to_string ((fun (i : option int) -> i) None) = "None")
let printable_option_test_some =  assert(to_string ((fun (i : option int) -> i) (Some 3)) = "(Some 3)") by compute()

let printable_either_test_l =  assert(to_string ((fun (i : either int int) -> i) (Inl 3)) = "(Inl 3)") by compute()
let printable_either_test_r =  assert(to_string ((fun (i : either int int) -> i) (Inr 3)) = "(Inr 3)") by compute()

let printable_char_test =  assert(to_string '?' = "?") by compute()

let printable_tuple3_test =  assert(to_string (Mktuple3 0 1 2)  = "(0, 1, 2)") by compute()


(*

  And the to_strings are not defined for these, but their
  Printable.to_strings are right so keep or ditch?

let printable_byte_test =  assert(to_string ? = "?")
let printable_int8_test =  assert(to_string ? = "?")
let printable_uint8_test =  assert(to_string ? = "?")
let printable_int16_test =  assert(to_string ? = "?")
let printable_uint16_test =  assert(to_string ? = "?")
let printable_int32_test =  assert(to_string ? = "?")
let printable_uint32_test =  assert(to_string ? = "?")
let printable_int64_test =  assert(to_string ? = "?")
let printable_uint64_test =  assert(to_string ? = "?")
let printable_int128_test =  assert(to_string ? = "?")
let printable_uint128_test =  assert(to_string ? = "?")
*)

(* Placeholders for float implementations. 
let printable_float_test =  assert(to_string ? = "?")
let printable_double_test =  assert(to_string ? = "?")
*) 

