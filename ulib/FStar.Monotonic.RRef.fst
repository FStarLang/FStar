module FStar.Monotonic.RRef

open FStar
open FStar.HyperHeap

open FStar.HyperStack
open FStar.HST

module HS = FStar.HyperStack
module HST = FStar.HST

let reln (a:Type) = a -> a -> Type

let monotonic (a:Type) (b:reln a) =
  (forall x. b x x)                             (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

//adding eternal region for now, since it is used with ralloc
type rid = r:rid{HS.is_eternal_region r}

abstract type m_rref (r:rid) (a:Type) (b:reln a) = x:HS.ref a{x.id = r}

let haseq_m_rref (r:rid) (a:Type) (b:reln a) 
    : Lemma (requires True)
	    (ensures (hasEq (m_rref r a b)))
	    [SMTPat (hasEq (m_rref r a b))]
    = ()

val as_rref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (rref r a)
let as_rref #r #a #b x = x.ref

val as_reference: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b  -> GTot (ref a)
let as_reference #r #a #b x = x

val m_contains : #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> m:t -> GTot bool
let m_contains #r #a #b mr m = HyperHeap.contains_ref (as_rref mr) m

let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:t) (m1:t) : GTot Type0 =
  HyperHeap.fresh_rref (as_rref mr) m0 m1

val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> GTot a
let m_sel #r #a #b h m = HyperHeap.sel h (as_rref m)

val m_upd: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> a -> GTot t
let m_upd #r #a #b h m v = HyperHeap.upd h (as_rref m) v

val m_alloc: #a:Type
          -> #b:reln a
	    -> r:rid
            -> init:a
            -> ST (m_rref r a b)
		(requires (fun _ -> monotonic a b))
		(ensures (fun h0 (m:m_rref r a b) h1 -> ralloc_post r init h0 (as_reference m) h1))
let m_alloc #a #b r init = ralloc r init

val m_read:#r:rid 
       -> #a:Type
       -> #b:reln a
       -> x:m_rref r a b
       -> ST a
            (requires (fun h -> h `contains` (as_reference x)))
            (ensures (deref_post (as_reference x)))
let m_read #r #a #b x = !x

val m_write:#r:rid 
        -> #a:Type
        -> #b:reln a
        -> x:m_rref r a b
        -> v:a
        -> ST unit
              (requires (fun h0 -> h0 `contains` (as_reference x) /\ b (m_sel h0.h x) v))
              (ensures (assign_post (as_reference x) v))
let m_write #r #a #b x v = x := v

inline type stable_on_t (#i:rid) (#a:Type) (#b:reln a) (r:m_rref i a b) (p:(t -> GTot Type0)) =
  forall h0 h1. p h0 /\ b (m_sel h0 r) (m_sel h1 r) ==> p h1
abstract type witnessed (p:(t -> GTot Type0)) = True

val witness: #r:rid
          -> #a:Type
          -> #b:reln a
          -> m:m_rref r a b
          -> p:(t -> GTot Type0)
          -> ST unit
                (requires (fun h0 -> p h0.h /\ stable_on_t m p))
                (ensures (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness #r #a #b m p = ()

assume val weaken_witness : p:(t -> GTot Type0) 
			  -> q:(t -> GTot Type0) 
			  -> Lemma
  ((forall h. p h ==> q h) /\ witnessed p ==> witnessed q)

val testify: p:(t -> GTot Type0)
          -> ST unit
               (requires (fun _ ->  witnessed p))
               (ensures (fun h0 _ h1 -> h0==h1 /\ p h1.h))
let testify p = admit() //intentionally admitted


val testify_forall: #a:Type -> #p:(a -> t -> Type0) 
       -> $s:squash (forall (x:a). witnessed (p x)) 
       -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:a). p x h1.h)))
let testify_forall #a #p $s = admit() //intentionally admitted


val m_recall: #r:rid -> #a:Type -> #b:reln a 
            -> m:m_rref r a b
	    -> ST unit 
	      (requires (fun h -> True))
	      (ensures (fun h0 _ h1 -> h0==h1 /\ h1 `contains` (as_reference m)))
let m_recall #r #a #b m = recall m


let rid_exists (r:rid) (h:t) = b2t(Map.contains h r)
// ex_rid: The type of a region id that is known to exist now and for ever more
type ex_rid = r:rid{witnessed (rid_exists r)}

assume val ex_rid_of_rid: r:rid -> ST ex_rid
  (fun h -> True)
  (fun h0 r' h1 -> r=r' /\ h0==h1)
