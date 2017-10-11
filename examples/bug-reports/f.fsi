module F

type T : unit -> Type

val lemma_1 : x:unit ->
  Lemma (requires True) (ensures (T x)) [SMTPat (T x)]

val lemma_2 : x:unit -> Lemma (ensures (T x))
