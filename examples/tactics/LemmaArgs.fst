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
module LemmaArgs

open FStar.Tactics

let lemma_example1 (a:int) (b:int{b <> a})
  :Lemma (requires True)
         (ensures b <> a)
  = ()

(* This one should work *)
let example0 x : Lemma (requires (x <> 5)) (ensures True) =
  assert (x <> 5) by (apply_lemma (quote lemma_example1))

[@(expect_failure [19])]
let example1 x : Lemma (requires (x == 5)) (ensures False) =
  assert (x <> 5) by (apply_lemma (quote lemma_example1))
