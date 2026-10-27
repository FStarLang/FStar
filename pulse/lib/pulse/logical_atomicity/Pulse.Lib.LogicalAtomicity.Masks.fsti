module Pulse.Lib.LogicalAtomicity.Masks

open Pulse.Lib.Core
open PulseCore.Observability
open FStar.Ghost
open FStar.ExtractAs
module I = Pulse.Lib.Core.Inv

// These masks name OPEN invariants (the opposite polarity to Iris's masks).
// Only run can turn a balanced action into an ordinary Pulse computation.
// The model implementation proves these combinators against Pulse semantics;
// extraction keeps only values, sequencing, and the lifted atomic operation.
[@@extract_as_impure_effect]
val action (a:Type u#a) (obs:observability)
  (before after:inames) (pre:slprop) (post:a -> slprop) : Type u#(max 4 a)

[@@erasable]
val gaction (a:Type u#a) (before after:inames)
  (pre:slprop) (post:a -> slprop) : Type u#(max 4 a)

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (_:unit) (x:a) (_:unit) -> x))]
val return (#a:Type u#a) (mask:inames) (x:a) (post:a -> slprop)
  : action a Neutral mask mask (post x) post

inline_for_extraction
[@@extract_as (`(fun (#a #b:Type0) (#o1 #o2 #m1 #m2 #m3 #p #q #r:unit)
  (f:a) (g:a -> Dv b) -> g f))]
val bind (#a:Type u#a) (#b:Type u#b)
  (#o1:observability) (#o2:observability { at_most_one_observable o1 o2 })
  (#m1 #m2 #m3:inames) (#p:slprop) (#q:a -> slprop) (#r:b -> slprop)
  (f:action a o1 m1 m2 p q)
  (g:(x:a -> action b o2 m2 m3 (q x) r))
  : action b (join_obs o1 o2) m1 m3 p r

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #m1 #m2 #p #q:unit) (_:unit) (f:a) -> f))]
val frame (#a:Type u#a) (#o:observability)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (r:slprop) (f:action a o m1 m2 p q)
  : action a o m1 m2 (p ** r) (fun x -> q x ** r)

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #opens #p #q:unit) (_:unit) (f:a) -> f))]
val lift_atomic (#a:Type u#a) (#o:observability)
  (#opens:inames) (#p:slprop) (#q:a -> slprop)
  (mask:inames { mask /! opens })
  (f:stt_atomic a #o opens p q)
  : action a o mask mask p q

val lift_ghost (#a:Type u#a) (#opens:inames) (#p:slprop) (#q:a -> slprop)
  (mask:inames { mask /! opens })
  (f:stt_ghost a opens p q)
  : gaction a mask mask p q

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#m1 #m2 #p #q:unit) (_:unit) -> ()))]
val ghost_to_action (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (f:gaction a m1 m2 p q)
  : action (erased a) Neutral m1 m2 p (fun x -> q x)

val bind_ghost (#a:Type u#a) (#b:Type u#b)
  (#m1 #m2 #m3:inames) (#p:slprop) (#q:a -> slprop) (#r:b -> slprop)
  (f:gaction a m1 m2 p q)
  (g:(x:a -> gaction b m2 m3 (q x) r))
  : gaction b m1 m3 p r

val frame_ghost (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (r:slprop) (f:gaction a m1 m2 p q)
  : gaction a m1 m2 (p ** r) (fun x -> q x ** r)

val action_to_ghost (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (f:action a Neutral m1 m2 p q)
  : gaction a m1 m2 p q

val sub_ghost (#a:Type u#a) (#m1 #m2:inames)
  (#p:slprop) (#q:a -> slprop)
  (p':slprop { p == p' })
  (q':(a -> slprop) { forall x. q x == q' x })
  (f:gaction a m1 m2 p q)
  : gaction a m1 m2 p' q'

val reindex_ghost (#a:Type u#a) (#m1 #m2:inames)
  (#p:slprop) (#q:a -> slprop)
  (before:inames { before == m1 }) (after:inames { after == m2 })
  (f:gaction a m1 m2 p q)
  : gaction a before after p q

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#m1 #m2 #p:unit) (x:a) (_ _:unit) -> x))]
val finish_ghost (#a:Type u#a) (#m1 #m2:inames) (#p:slprop)
  (x:a) (post:a -> slprop) (f:gaction unit m1 m2 p (fun _ -> post x))
  : action a Neutral m1 m2 p post

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #p #q:unit) (_:unit) (f:unit -> Dv a) -> f ()))]
val run (#a:Type0) (#o:observability) (#p:slprop) (#q:a -> slprop)
  (opens:inames)
  (f:(mask:inames { mask /! opens } -> action a o mask mask p q))
  : stt_atomic a #o opens p q

inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #p #q:unit) (f:a) -> f))]
val run_closed (#a:Type0) (#o:observability) (#p:slprop) (#q:a -> slprop)
  (f:action a o emp_inames emp_inames p q)
  : stt_atomic a #o all_inames p q

val open_invariant (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : gaction unit mask (add_inv mask i)
      (I.inv i p)
      (fun _ -> I.inv i p ** I.somewhere (later p))

val close_invariant (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : gaction unit (add_inv mask i) mask
      (I.inv i p ** I.somewhere (later p))
      (fun _ -> I.inv i p)
