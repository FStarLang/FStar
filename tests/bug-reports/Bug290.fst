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
module Bug290

val id : nat -> Tot nat
let id x = x

assume val test : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (fst r) = fst r)) (*Succeeds*)

assume val test2 : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (snd r) = snd r)) (*Succeeds*)

assume val test3 : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (fst r) = snd r)) (*Fails*)

assume val test4 : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (snd r) = fst r)) (*Fails*)

