(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --verify_module FscalarLemmas ;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst
  --*)

module FscalarLemmas

open FStar.Ghost

val lemma_1: x:int ->
  Lemma 
    (requires (True))
    (ensures (x * 0 = 0 /\ 0 * x = 0))
let lemma_1 x = ()

val lemma_2: x:int -> y:int ->
  Lemma 
    (requires (y = 0))
    (ensures (x * y = 0 /\ y * x = 0))
let lemma_2 x y = ()

val lemma_3: x:nat -> 
  Lemma 
    (requires (x <> 0))
    (ensures (x-1 >= 0))
let lemma_3 x = ()

val lemma_4: x:nat -> y:nat -> 
  Lemma 
    (requires (x <> y /\ x >= y))
    (ensures (x > y))
let lemma_4 x y = ()

val helper_lemma_1:
  i:nat -> len:nat -> v:erased nat -> 
  Lemma (requires (i < len /\ len <= reveal v)) (ensures (i < reveal v))
let helper_lemma_1 i len v = ()

