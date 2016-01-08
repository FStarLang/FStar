(*--build-config
    options:--admit_fsi FStar.Set --verify_module Bug;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst
  --*)

module Bug
open FStar.Heap

let sixty_four = 64

type lint (n:nat) = x:nat{ x < n }

type box = | Box: v:ref (lint 64) -> box

val upd': h:heap -> =r:ref 'a -> v:'a -> Tot heap
let upd' h r v = Heap.upd h r v

val fails:
  h:heap -> h':heap -> b:box -> v:lint 64 ->
  Lemma
    (requires (contains h (Box.v b) 
  	      /\ h'=Heap.upd h (Box.v b) v))
    (ensures modifies !{Box.v b} h h')
let fails h h' b v = ()  

// type box' = | Box': v:FStar.Heap.ref (lint sixty_four) -> box'

// val works:
//   h:heap -> h':heap -> b:box'{contains h (Box'.v b)} -> v:lint 64 ->
//   Lemma
//     (requires (h'==Heap.upd h (Box'.v b) v))
//     (ensures (
//       ((modifies !{Box'.v b} h h'))      
//       ))
// let works h h' b v = 
//   ()  
