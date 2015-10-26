module Test

val test: p:(int -> Tot bool) ->
  Lemma (requires (forall (i:int). {:pattern (p i)} (i >= 0) ==> p (i+1)))
	(ensures (forall (i:int). (i >= 1) ==> p i))
let test p = ()
