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
module Bug259

// this is like a runtime env
type env value = nat -> Tot value

// defining a value datatype
noeq type value =
  | C: nat -> value
  | F: env value -> value

// defining a translation function on values recursively with the translation
// function on env
assume val preceds_axiom: en:env value -> x:nat -> Lemma (ensures (en x << en))

val tr_v : v:value -> Tot value (decreases %[v])
val tr_en: en:env value -> nat -> Tot value (decreases %[en])

let rec tr_v v =
  match v with
    | C n    -> v
    | F en -> F (tr_en en)

and tr_en en x = preceds_axiom en x; tr_v (en x)
//Succeeds using this hack
//
//and tr_en en =
//  let _ = () in
//  fun x -> precedes_axiom en x; tr_v (en x)

// some assumptions
assume val v:value
assume val en:env value
assume val n:nat

// this should succeed
let t = assert (tr_v (F en) == F (tr_en en))
