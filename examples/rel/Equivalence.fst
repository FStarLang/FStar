module Equivalence

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

(* lots of thunking going on *)
val if_left : a:Type -> e:(unit -> STNull bool) ->
    e1:(unit -> STNull a) -> e2:(unit -> STNull a) -> h0:heap ->
  Lemma (requires (reify (e()) h0 == (true, h0)))
        (ensures (reify (if e() then e1() else e2()) h0 == reify (e1()) h0))
let if_left a e e1 e2 h0 = ()

(* then trying to go for non-trivial pre- and postconditions *)
let if_left_wp (a:Type)
    (epre:_)  (epost:_)  (e:(unit -> ST bool epre epost))
    (e1pre:_) (e1post:_) (e1:(unit -> ST a e1pre e1post))
    (e2pre:_) (e2post:_) (e2:(unit -> ST a e2pre e2post)) (h0:heap) :
  Lemma (requires (epre h0 /\ reify (e()) h0 == (true, h0)))
        (ensures ((epre h0 /\ e1pre h0 /\ e2pre h0) ==>
                     reify (if e() then e1()
                                   else e2()) h0 == reify (e1()) h0))
  = ()
(* Stuck: assertion fail for the e1() and e2(), still no clue why *)
