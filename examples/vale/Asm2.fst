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
