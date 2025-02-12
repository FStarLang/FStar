(*
   Copyright 2008-2025 Microsoft Research

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
module FStar.Tuple10
(* Autogenerated by mk_tuple.sh *)

type t
  (t1 : (Type))
  (t2 : (Type))
  (t3 : (Type))
  (t4 : (Type))
  (t5 : (Type))
  (t6 : (Type))
  (t7 : (Type))
  (t8 : (Type))
  (t9 : (Type))
  (t10 : (Type))
= | Mk :
      _1 : t1 ->
      _2 : t2 ->
      _3 : t3 ->
      _4 : t4 ->
      _5 : t5 ->
      _6 : t6 ->
      _7 : t7 ->
      _8 : t8 ->
      _9 : t9 ->
      _10 : t10 ->
      t t1 t2 t3 t4 t5 t6 t7 t8 t9 t10

let tuple10 = t
