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
module Bug151

open FStar.Array
open FStar.Seq

assume new type p: int -> nat -> Type

type int_1 = x:int{ p x 1 }
type int_2 = x:int{ p x 2 }

type seq_int_1 = seq int_1
type seq_int_2 = seq int_2

assume val eval:
  a:seq int -> len:nat{ len <= length a } -> Tot int

assume val bla2:
  a:seq_int_1{ length a = 10 } ->
  b:seq_int_2{ (length b = length a) /\ (eval a (length a) = eval b (length b)) }
