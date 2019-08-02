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
module X64.Vale.Lemmas_i
open X64.Machine_s
open X64.Vale.State_i
open FStar.UInt
module S = X64.Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2"

let eval_while b c n s0 s1 : Type0 = admit ()

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()

let lemma_block (b0:codes) (s0:state) (sN:state) =
  let c1::b1 = b0 in
  let s0' = state_to_S s0 in
  // let Some s1' = S.eval_code c1 fuel s0' in
  // let s1 = state_of_S s1' in
  // (s1, c1, b1)
  admit () // TODO

let lemma_empty (s0:state) (sN:state) =
  assume False; // TODO
  s0

let lemma_ifElse (ifb:S.ocmp) (ct:code) (cf:code) (s0:state) (sN:state) =
  (eval_ocmp s0 ifb, s0)

let lemma_while b c s0 sN = admit () // TODO
let lemma_whileTrue b c n s0 sN = admit () // TODO
let lemma_whileFalse b c s0 sN = admit () // TODO

