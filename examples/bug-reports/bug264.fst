module Bug264

open FStar.Heap
open FStar.ST

type ref_identity (f:ref (nat -> Tot nat)) (h:heap) =
    (contains h f /\ (forall (n:nat). (sel h f) n = n))  // Say that f points to the identity
