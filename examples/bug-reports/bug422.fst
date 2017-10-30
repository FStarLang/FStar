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
