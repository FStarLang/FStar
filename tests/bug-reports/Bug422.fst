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
module Bug422
open FStar.Heap

let sixty_four = 64

type lint (n:nat) = x:nat{ x < n }

noeq type box = | Box: v:ref (lint 64) -> box

val upd': h:heap -> $r:ref 'a -> v:'a -> GTot heap
let upd' h r v = Heap.upd h r v

val fails:
  h:heap -> h':heap -> b:box -> v:lint 64 ->
  Lemma
    (requires (contains h (Box?.v b)
  	      /\ h'==Heap.upd h (Box?.v b) v))
    (ensures modifies !{Box?.v b} h h')
let fails h h' b v = ()

noeq type box' = | Box': v:FStar.Heap.ref (lint sixty_four) -> box'

val works:
  h:heap -> h':heap -> b:box'{contains h (Box'?.v b)} -> v:lint 64 ->
  Lemma
    (requires (h'==Heap.upd h (Box'?.v b) v))
    (ensures (
      ((modifies !{Box'?.v b} h h'))
      ))
let works h h' b v =
  ()
