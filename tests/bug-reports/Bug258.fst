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
module Bug258

noeq type value : Type0 =
  | V_clos : env -> nat -> value
and env = | E: f:(nat -> Tot value) -> env

assume val pr_axiom: en:env -> x:nat -> Lemma (ensures (en.f x << en))

val slice_v : v:value -> Tot value //(decreases v) // Works with this clause

val slice_en: en:env -> n:nat -> Tot value (decreases en)

let rec slice_v v = match v with
  | V_clos en x ->
    V_clos (E (slice_en en)) x
and slice_en en y = pr_axiom en y; slice_v (en.f y)
