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
module Asm2

module Map=FStar.Map
let map = Map.t
let op_String_Access = Map.sel
let op_String_Assignment = Map.upd
let contains = Map.contains

type state = map int int

let lemma_load (src:int) (offset:int) (s0:state { contains s0 (src + offset) }) :
  Tot (dst:int { dst == s0.[src + offset]}) =
  s0.[src + offset]

let lemma_store (dst:int) (offset:int) (src:int) (s0:state { contains s0 (dst + offset) }) :
  Tot (s1:state { s1 == (s0.[dst + offset] <- src)}) =
  s0.[dst + offset] <- src

let lemma_copy (r3:int) (s0:state
    { let a = r3 in
      let m = s0 in
          contains m (a + 0)
       /\ contains m (a + 1)
       /\ contains m (a + 2)
       /\ contains m (a + 20)
       /\ contains m (a + 21)
       /\ contains m (a + 22)}) :
  Tot (sN:state {
      let a = r3 in
      let m0 = s0 in
      let mN = sN in
          mN.[a + 20] == m0.[a + 0]
       /\ mN.[a + 21] == m0.[a + 1]
       /\ mN.[a + 22] == m0.[a + 2]}) =
  let r0 = lemma_load r3 0 s0 in
  let r1 = lemma_load r3 1 s0 in
  let r2 = lemma_load r3 2 s0 in
  let s4 = lemma_store r3 20 r0 s0 in
  let s5 = lemma_store r3 21 r1 s4 in
  let s6 = lemma_store r3 22 r2 s5 in
  s6
