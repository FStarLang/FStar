module PCM.POD

open FStar.PCM

val pod: Type u#a -> Type u#a
val none: pod 'a
val some: 'a -> pod 'a

val is_some: pod 'a -> prop
val some_v: x:pod 'a{is_some x} -> y:'a{x == some y}

val pod_pcm (a:Type): AggregateRef.refined_one_pcm (pod a)

val none_is_unit (a:Type): Lemma (none == one (pod_pcm a)) [SMTPat (one (pod_pcm a))]

val is_some_some (v:'a): Lemma (is_some (some v)) [SMTPat (some v)]

val some_none_distinct (v:pod 'a)
: Lemma (requires is_some v) (ensures ~ (v == none)) [SMTPat (is_some v)]

val some_compatible (v w:pod 'a)
: Lemma (requires compatible (pod_pcm 'a) v w /\ is_some v) (ensures is_some w)
  [SMTPat (compatible (pod_pcm 'a) v w); SMTPat (is_some v)]
  
val some_valid_write (v w: pod 'a)
: Lemma
    (requires is_some v /\ is_some w)
    (ensures AggregateRef.valid_write (pod_pcm 'a) v w)
  [SMTPat (is_some v); SMTPat (is_some w)]
