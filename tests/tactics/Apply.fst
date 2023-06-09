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
module Apply

open FStar.Mul
open FStar.Tactics.V2

assume val x : int

val refl : (a:Type) -> (x:a) -> Lemma (x == x)
let refl a x = ()

let tau () : Tac unit =
    apply_lemma (quote refl)

let lem1 = assert (x == x) by tau ()
