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
module StringNormalization

(* Testing string support in the normalizer *)

open FStar.String
open FStar.Char

let _ = assert_norm("a" ^ "b" == "ab")

let _ = assert_norm(string_of_int 123 == "123")

let _ = assert_norm(string_of_bool true == "true")

let _ = assert_norm(string_of_bool false == "false")

let _ = assert_norm("a" ^ string_of_int 123 ^ "b" ^ string_of_bool true == "a123btrue")

let _ = assert_norm (List.Tot.map int_of_char (list_of_string "") == [])

let _ = assert_norm (list_of_string "a8X" == ['a'; '8'; 'X'])

// int_of_char doesn't reduce, so this fails
//let _ = assert_norm (List.Tot.map int_of_char (list_of_string "a8X") == [97; 56; 88])

let _ = assert_norm (string_of_list ['a'; '8'; 'X'] == "a8X")

let _ = assert_norm (concat "." ["FStar";"Mul";"op_Star"] == "FStar.Mul.op_Star")
