module Bug251
val t : unit -> Type
val lemma_1 : x:unit -> Lemma (requires True) (ensures (t x)) [SMTPatT (t x)]
val lemma_2 : x:unit -> Lemma (ensures (t x))
