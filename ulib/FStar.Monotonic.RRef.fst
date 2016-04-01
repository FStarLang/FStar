module FStar.Monotonic.RRef
open FStar
open FStar.ST
open FStar.HyperHeap

let reln (a:Type) = a -> a -> Type

let monotonic (a:Type) (b:reln a) =
  (forall x. b x x)                             (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

abstract type m_rref (r:rid) (a:Type) (b:reln a) = rref r a
 
val as_rref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (rref r a)
let as_rref #r #a #b x = x

val m_contains : #r:rid -> #a:Type -> #b:reln a -> r:m_rref r a b -> m:t -> GTot bool
let m_contains #r #a #b r m = HyperHeap.contains_ref (as_rref r) m 

val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> GTot a
let m_sel #r #a #b h m = HyperHeap.sel h m

val m_upd: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> a -> GTot t
let m_upd #r #a #b h m v = HyperHeap.upd h m v

val m_alloc: #a:Type
          -> #b:reln a
	  -> r:rid
          -> init:a
          -> ST (m_rref r a b)
               (requires (fun _ -> monotonic a b))
	       (ensures (fun h0 (m:m_rref r a b) h1 -> ralloc_post r init h0 (as_rref m) h1))
let m_alloc #a #b r init = ST.ralloc r init

val m_read:#r:rid 
       -> #a:Type
       -> #b:reln a
       -> x:m_rref r a b
       -> ST a
            (requires (fun h -> True))
            (ensures (deref_post (as_rref x)))
let m_read #r #a #b x = !x

val m_write:#r:rid 
        -> #a:Type
        -> #b:reln a
        -> x:m_rref r a b
        -> v:a
        -> ST unit
              (requires (fun h0 -> b (m_sel h0 x) v))
              (ensures (assign_post (as_rref x) v))
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
                (requires (fun h0 -> p h0 /\ stable_on_t m p))
                (ensures (fun h0 _ h1 -> h0=h1 /\ witnessed p))
let witness #r #a #b m p = ()

val testify: p:(t -> GTot Type0)
          -> ST unit
               (requires (fun _ ->  witnessed p))
               (ensures (fun h0 _ h1 -> p h1))
let testify p = admit() //intentionally admitted

val m_recall: #r:rid -> #a:Type -> #b:reln a 
            -> m:m_rref r a b
	    -> ST unit 
	      (requires (fun h -> True))
	      (ensures (fun h0 _ h1 -> h0=h1 /\ m_contains m h1))
let m_recall #r #a #b m = admit() //intentionally admitted
