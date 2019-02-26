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

open FStar.Char
open FStar.String

let _ = assert (string_of_int 123 == "123")

let _ = assert (string_of_bool true == "true")

let _ = assert (string_of_bool false == "false")

let _ = assert (List.Tot.map int_of_char (list_of_string "") == [])

let _ = assert (list_of_string "a8X" == ['a'; '8'; 'X'])

let _ = assert (List.Tot.map int_of_char (list_of_string "a8X") == [97; 56; 88])

let _ = assert (string_of_list ['a'; '8'; 'X'] == "a8X")

let _ = assert (concat "." ["FStar";"Mul";"op_Star"] == "FStar.Mul.op_Star")

let _ = assert_norm (strlen "Hello" == 5)

let _ = assert_norm (length "Hello" == 5)

let _ = assert (make 5 'f' = "fffff")

let _ = assert_norm (string_of_char 'a' == "a")

let _ = assert (split ['a'; 'b'] "ccaddbee" == ["cc"; "dd"; "ee"])

let _ = assert (split [','; ';'] "cc,dd;ee;" == ["cc"; "dd"; "ee"; ""])
let _ = assert (split [','; ';'] ",cc,dd;ee;" == ["cc"; "dd"; "ee"; ""])
let _ = assert (split [','; ';'] ",cc,dd;ee;;" == ["cc"; "dd"; "ee"; ""; ""])

let _ = assert ("a" `strcat` "b" == "ab")
let _ = assert ("a" `strcat` string_of_int 123 `strcat` "b" `strcat` string_of_bool true == "a123btrue")

let _ = assert ("a" ^ "b" == "ab")
let _ = assert ("a" ^ string_of_int 123 ^ "b" ^ string_of_bool true == "a123btrue")

let _ = assert (concat "," ["a"; "b"; "c"] == "a,b,c")
let _ = assert (concat "," [] == "")

let _ = assert (compare "AAA" "AAB" == (-1))
let _ = assert (compare "AAA" "AA" == 1)
let _ = assert (compare "AAA" "AAA" == 0)
let _ = assert (compare "AAA" "BAA" == (-1))

let _ = assert (lowercase "Hello World" == "hello world")
let _ = assert (uppercase "Hello World" == "HELLO WORLD")

let _ =
  assert_norm (length "Hello" == 5); (* awkward *)
  assert (index "Hello" 4 == 'o')

let _ = assert (index_of "Hello" 'o' == 4)
let _ = assert (index_of "Hello" 'x' == (-1))

let _ =
  assert_norm (length "Hello World" == 11); (* awkward *)
  assert (sub "Hello World" 3 4 == "lo W")

let _ =
  assert (norm [nbe; primops] ("abc" ^ "def") == "abcdef")
