(*
   Copyright 2024 Microsoft Research

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

module FStar.String.Base
open FStar.String

///  Partial equivalence properties.

let streq_upto s1 s2 (pos: nat) =
  (pos <= strlen s1 /\ pos <= strlen s2 /\
   (forall (i: nat{i < pos}). index s1 i = index s2 i))

let streq_upto_min s1 s2 (pos: int{pos < (min (strlen s1) (strlen s2))}) =
  (forall (i: nat{i <= pos}). index s1 i = index s2 i)

///  The boolean form of streq.

val streq_upto' s1 (s2: string{strlen s1 = strlen s2}) (to: nat{to <= strlen s1}):
  Tot (b:bool{b <==> streq_upto s1 s2 to})
