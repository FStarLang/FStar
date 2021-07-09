module FStar.PCM.POD

open FStar.PCM
open FStar.PCM.Extras

val pod: Type u#a -> Type u#a

val none: Ghost.erased (pod 'a)
val some: Ghost.erased 'a -> Ghost.erased (pod 'a)

val is_some: Ghost.erased (pod 'a) -> prop
val some_v: x:pod 'a{is_some x} -> GTot (y:'a{x == Ghost.reveal (some y)})

val pod_pcm (a:Type): refined_one_pcm (pod a)

val none_is_unit (a:Type): Lemma (Ghost.reveal none == one (pod_pcm a)) [SMTPat (one (pod_pcm a))]

val is_some_some (v:Ghost.erased 'a): Lemma (is_some (some v)) [SMTPat (some v)]

val some_none_distinct (v:pod 'a)
: Lemma (requires is_some v) (ensures ~ (v == Ghost.reveal none)) [SMTPat (is_some v)]

val some_compatible (v w:pod 'a)
: Lemma (requires compatible (pod_pcm 'a) v w /\ is_some v) (ensures is_some w)
  [SMTPat (compatible (pod_pcm 'a) v w); SMTPat (is_some v)]
  
val some_valid_write (v w: pod 'a)
: Lemma
    (requires is_some v /\ is_some w)
    (ensures AggregateRef.valid_write (pod_pcm 'a) v w)
  [SMTPat (is_some v); SMTPat (is_some w)]
