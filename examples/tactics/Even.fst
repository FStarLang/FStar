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
module Even

open FStar.Tactics

type unat = | Z : unat | S : unat → unat
let rec nat2unary (n: nat) : Tot unat = if n = 0 then Z else S (nat2unary (n - 1))
type even : unat → Type = | Even_Z : even Z | Even_SS : #n: unat → even n → even (S (S n))

let prove_even () = compute (); ignore (repeat (fun () -> apply (`Even_SS))); apply (`Even_Z)

let even10 : even (normalize_term (nat2unary 10)) = synth prove_even
