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
module Evens
type unary_nat =
| U0 : unary_nat
| US : unary_nat -> unary_nat

type even : unary_nat -> Type =
| Even0 : even U0
| Even_SSn : n: unary_nat -> even n -> even (US (US n))

[@plugin]
let rec nat2unary (n: nat) : unary_nat = 
  if n = 0 then U0  else US (nat2unary (n - 1))

open FStar.Tactics

let even0 () : Lemma (even U0) = ()
let evenSSn (n: unary_nat) : 
  Lemma (requires even n)
        (ensures even (US (US n))) =
 // What's the proper way to do this?
 assert_by_tactic (even n ==> even (US (US n)))
                  (fun () -> ignore (implies_intro ());
                          squash_intro ();
                          apply (`Even_SSn);
                          assumption ())
[@plugin]
let prove_even () : Tac unit =
   ignore (repeat (fun () -> apply_lemma (`evenSSn)));
   apply_lemma (`even0)
