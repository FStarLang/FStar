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
    (epre:_)  (epost:_) (e1pre:_) (e1post:_) (e2pre:_) (e2post:_) 
    (e:(unit -> ST bool epre epost))
    (e1:(unit -> ST a e1pre e1post))
    (e2:(unit -> ST a e2pre e2post)) (h0:heap{epre h0 /\ e1pre h0 /\ e2pre h0 /\
                                             reify (e()) h0 == (true, h0)}) :
  Lemma (reify (if refine_st e () then e1 () else e2 ()) h0 ==  //using refine_st to establish that after e () the heap remains same
         reify (e1 ()) h0)
  = ignore (reify (refine_st e ()) h0) (* AR: not sure why this is required *)

(* here's another way ... also with some mysterious requirements *)
let if_left_wp' (a:Type)
    (epre:_)  (e:(unit -> ST bool epre (fun h0 x h1 -> h0 == h1)))
    (e1pre:_) (e1:(unit -> ST a e1pre (fun _ _ _ -> True)))
    (e2pre:_) (e2:(unit -> ST a e2pre (fun _ _ _ -> True)))
    (h0:heap{epre h0 /\ e1pre h0 /\ e2pre h0}) :
  Lemma (requires (b2t (fst (reify (e()) h0)))) (* CH: for some reason can't just replace this with `fst (reify (e()) h0) = true` *) (* AR: we could, but somehow z3 needs help, could be some trigger issues ... *)
        (ensures (reify (if e() then e1() else e2()) h0 == reify (e1()) h0))
  = ignore (reify (e ()) h0)
