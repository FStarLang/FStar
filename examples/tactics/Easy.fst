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
module Easy

open FStar.Tactics

val plus_assoc : x:int -> y:int -> z:int -> Lemma ((x + y) + z == x + (y + z))
let plus_assoc = easy

val plus_comm : x:int -> y:int -> Lemma (x + y == y + x)
let plus_comm = easy
