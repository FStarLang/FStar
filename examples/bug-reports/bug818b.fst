module Bug818b

open FStar.ST
open FStar.Heap

assume type matrix
type sshuffle = heap -> Tot heap
val siter: n:nat -> (f: 'a -> Tot 'a) -> 'a -> 'a
let rec siter n f x = if n = 0 then x else siter (n-1) f (f x)

type shuffle (spec: sshuffle) =
  m:matrix -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> spec h0 == spec h0))

val iter: n:nat -> spec: sshuffle -> body: shuffle spec -> shuffle (siter (n+1) spec)
let rec iter n spec body m =
  if n <> 0 then (
    body m;
    admit();
    iter (n - 1) spec body m )
