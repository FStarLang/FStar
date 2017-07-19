module Lang

open FStar.Seq
open FStar.Set

assume val size:nat

type addr = n:nat{n < size}

type heap = set addr * (s:seq nat{length s = size})

let dom (s:heap) :set addr = fst s

let memory (s:heap) :(s:seq nat{length s = size}) = snd s

let op_String_Access (s:heap) (id:addr) :nat = index (memory s) id
let op_String_Assignment (s:heap) (id:addr) (v:nat) :heap = (dom s, Seq.upd (memory s) id v)
let contains (s:heap) (id:addr) :Type0 = Set.mem id (dom s)

let disjoint (s1:heap) (s2:heap) :Type0 = Set.disjoint (dom s1) (dom s2)

let join (s1:heap) (s2:heap{disjoint s1 s2}) :(s:heap{dom s == Set.union (dom s1) (dom s2)              /\
                                                         (forall (i:addr). s1 `contains` i ==> s.[i] == s1.[i]) /\
                                                         (forall (i:addr). s2 `contains` i ==> s.[i] == s2.[i])})
  = admit ()

type loop_result (a:Type0) =
  | Done : v:a -> loop_result a
  | Again: i:nat -> loop_result a

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b
  | Loop  : #a:Type0 -> i:nat -> f:(nat -> command (loop_result a)) -> command a
  | Fail  : #a:Type0 -> command a
  | Read  : id:addr -> command nat
  | Write : id:addr -> v:nat -> command unit
  | Alloc : command addr
  | Free  : id:addr -> command unit

(*
 * a bit hacky, since a program may not terminate
 *)
assume val interpreted_in (#a:Type0) (c:command a) (h:heap) :Tot (a * heap)

type heap_predicate = heap -> Type0

let emp :heap_predicate
  = fun h ->
    let dom, _ = h in
    dom == Set.empty

let points_to (id:addr) (n:nat) :heap_predicate
  = fun h ->
    let dom, m = h in
    dom == Set.singleton id /\ index m id == n

let lift (phi:Type0) :heap_predicate
  = fun h -> phi /\ emp h

let exists_x (#a:Type0) (pred:a -> heap_predicate) :heap_predicate
  = fun h -> exists (x:a). pred x h

let star (p:heap_predicate) (q:heap_predicate) :heap_predicate
  = fun h -> exists (h1:heap) (h2:heap). disjoint h1 h2 /\ h == join h1 h2 /\ p h1 /\ q h2

let iff (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h <==> q h

let imp (p:heap_predicate) (q:heap_predicate) :Type0 = forall (h:heap). p h ==> q h

type c_pre            = heap_predicate
type c_post (a:Type0) = a -> heap_predicate

type hoare_triple (#a:Type0) (pre:c_pre) (c:command a) (post:c_post a)
  = forall (h0:heap) (h1:heap) (r:a). (pre h0 /\ (c `interpreted_in` h0 == (r, h1))) ==> post r h1

(* all the following rules are conditioned on termination *)
val lemma_return (#a:Type0) (v:a) (c:command a{c == Return v}) (pre:c_pre)
  :Lemma (requires True)  
         (ensures (let post :(c_post a) = fun r -> pre `star` (lift (r == v)) in
                   hoare_triple pre c post))

val lemma_bind (#a:Type0) (#b:Type0) (c1:command a) (c2:a -> command b) (c:command b{c == Bind c1 c2})
  (pre:c_pre) (post:c_post b)
  :Lemma (requires (exists (q:c_post a). (hoare_triple pre c1 q /\ (forall (r:a). hoare_triple (q r) (c2 r) post))))
	 (ensures  (hoare_triple pre c post))

val lemma_loop (#a:Type0) (i:nat) (f:nat -> command (loop_result a)) (c:command a{c == Loop i f}) (inv:c_post (loop_result a))
  :Lemma (requires (forall (j:nat). hoare_triple (inv (Again j)) (f j) inv))
         (ensures  (hoare_triple (inv (Again i)) c (fun r -> inv (Done r))))

val lemma_fail (#a:Type0) (c:command a{c == Fail #a})
  :Lemma (requires True)
         (ensures  (hoare_triple (lift False) c (fun _ -> lift False)))

val lemma_consequence (#a:Type0) (c:command a) (p':c_pre) (q':c_post a)
  :Lemma (requires (forall (p:c_pre) (q:c_post a). hoare_triple p c q /\ p' `imp` p /\ (forall r. q r `imp` q' r)))
         (ensures  (hoare_triple p' c q'))
