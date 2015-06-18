module ScopedWhile3
type vector (a:Type) (n:nat) = k:nat{k < n}-> Tot a
type smem
assume val refExistsInMem: #a:Type -> ref a -> smem -> Tot bool
assume val loopkupRef : #a:Type -> r:ref a -> m:smem{refExistsInMem r m==true} -> Tot bool

type innerLoopInv (n:nat) (res:ref (vector bool n)) (m:smem) =
  refExistsInMem res m
  /\ loopkupRef res m
