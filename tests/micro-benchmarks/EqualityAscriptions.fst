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
module EqualityAscriptions

let test () : unit =
  let _ = (λ x → 2) $: ℤ → ℤ in
  ()

[@@ expect_failure]
let test1 () : unit =
  //type annotation on the binder is not equal to int
  let _ = (λ (x:ℕ) → 2) $: ℤ → ℤ in
  ()

[@@ expect_failure]
let test1 () : unit =
  //return type of the lambda is not nat, it is int
  let _ = (λ x → 2) $: ℤ → ℕ in
  ()

let test1 () : unit =
  //but we can subtype the body to nat
  let _ = (λ x → 2 <: ℕ) $: ℤ → ℕ in
  ()
