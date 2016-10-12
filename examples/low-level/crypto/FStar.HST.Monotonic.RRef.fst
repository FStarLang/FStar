module FStar.HST.Monotonic.RRef

open FStar
open FStar.HST
open FStar.HyperHeap
open FStar.HyperStack

type rid = r:HyperHeap.rid{is_eternal_region r}

let reln (a:Type) = a -> a -> Type

let monotonic (a:Type) (b:reln a) =
  (forall x. b x x)                          (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)  (* transitive *)

abstract type m_rref (r:rid) (a:Type) (b:reln a) = mr:ref a{mr.id = r}

assume HasEq_m_rref: forall (r:rid) (a:Type) (b:reln a).{:pattern (hasEq (m_rref r a b))} hasEq (m_rref r a b)

val as_ref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (ref a)
let as_ref #r #a #b x = x

val as_rref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (rref r a)
let as_rref #r #a #b x = x.ref

val m_contains : #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> m:mem -> GTot bool
let m_contains #r #a #b mr m = HyperHeap.contains_ref (as_rref mr) m.h

let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:mem) (m1:mem) : GTot Type0 =
  HyperHeap.fresh_rref (as_rref mr) m0.h m1.h

val m_sel: #r:rid -> #a:Type -> #b:reln a -> m:mem -> m_rref r a b -> GTot a
let m_sel #r #a #b m mr = HyperStack.sel m (as_ref mr)

val m_upd: #r:rid -> #a:Type -> #b:reln a -> m:mem{Map.contains m.h r} -> m_rref r a b -> a -> GTot mem
let m_upd #r #a #b m mr v = HyperStack.upd m mr v

val m_alloc: #a:Type -> #b:reln a -> r:rid -> init:a -> ST (m_rref r a b)
  (requires (fun _ -> monotonic a b))
  (ensures  (fun m0 mref m1 -> ralloc_post r init m0 (as_ref mref) m1))
let m_alloc #a #b r init = ralloc #a r init

val m_read: #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> STL a
  (requires (fun m -> m_contains mr m))
  (ensures  (deref_post (as_ref mr)))
let m_read #r #a #b mr = !mr

val m_write: #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> v:a -> STL unit
  (requires (fun m0 -> m_contains mr m0 /\ b (m_sel m0 mr) v))
  (ensures (assign_post (as_ref mr) v))
let m_write #r #a #b mr v = mr := v

unfold type stable_on_mem (#i:rid) (#a:Type) (#b:reln a) (r:m_rref i a b) (p:mem -> GTot Type0) =
  forall m0 m1. p m0 /\ b (m_sel m0 r) (m_sel m1 r) ==> p m1

abstract type witnessed (p:mem -> GTot Type0) = True

val witness: #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> p:(mem -> GTot Type0) ->
  STL unit
  (requires (fun m0 -> p m0 /\ stable_on_mem mr p))
  (ensures  (fun m0 _ m1 -> m0==m1 /\ witnessed p))
let witness #r #a #b mr p = ()

assume val weaken_witness : p:(mem -> GTot Type0) -> q:(mem -> GTot Type0) ->
  Lemma ((forall h. p h ==> q h) /\ witnessed p ==> witnessed q)

val testify: p:(mem -> GTot Type0) -> STL unit
  (requires (fun _ ->  witnessed p))
  (ensures  (fun m0 _ m1 -> m0==m1 /\ p m1))
let testify p = admit() //intentionally admitted

val testify_forall: #a:Type -> #p:(a -> mem -> Type0)
  -> $s:squash (forall (x:a). witnessed (p x))
  -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:a). p x h1)))
let testify_forall #a #p $s = admit() //intentionally admitted

val m_recall: #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> ST unit
  (requires (fun m0 -> True))
  (ensures  (fun m0 _ m1 -> m0==m1 /\ m_contains mr m1 /\ (as_ref mr).id = r))
let m_recall #r #a #b mr = FStar.HST.recall mr

let rid_exists (r:rid) (m:mem) = b2t(Map.contains m.h r)

// ex_rid: The type of a region id that is known to exist now and for ever more
type ex_rid = r:rid{witnessed (rid_exists r)}

assume val ex_rid_of_rid: r:rid -> ST ex_rid
  (fun m -> True)
  (fun m0 r' m1 -> r=r' /\ m0==m1)
