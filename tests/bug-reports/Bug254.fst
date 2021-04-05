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
module Bug254
open FStar.List

val foo : list nat -> Tot bool
let foo _ = true

val bar : ms1:list (nat * nat)
        -> ms2:list (nat * nat){mapT #_ #nat fst ms1 = mapT #_ #nat fst ms2}
        -> Lemma
        (requires (foo (mapT fst ms1)))
        (ensures true)
let bar ms1 ms2 =
let x = mapT fst ms1 in
let y = mapT fst ms2 in
(* this fails, but removing any one of the assertions below succeeds *)
let _ = assert (foo x) in
let _ = assert (x = y) in
()
