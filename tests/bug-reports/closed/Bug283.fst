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
module Bug283

assume new type block: Type0
assume HasEq_block: hasEq block

assume val xor : block -> block -> Tot block

assume XOR_Laws:forall a b.{:pattern (xor a b)} xor a b = xor b a /\ xor (xor a b) a = b
val test2 : unit -> Lemma (forall a b. xor (xor a b) b = a)
let test2 () = ()
