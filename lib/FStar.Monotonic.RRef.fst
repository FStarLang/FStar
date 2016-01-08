(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.HyperHeap;
    other-files:FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst hyperHeap.fsi stHyperHeap.fst
 --*)
module FStar.Monotonic.RRef
open FStar
open FStar.ST
open FStar.HyperHeap

kind Reln (a:Type) = a -> a -> Type

type monotonic (a:Type) (b:Reln a) =
  (forall x. b x x)                           (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

type stable : #a:Type -> (a -> Type) -> Reln a -> Type =
  fun (a:Type) (p:(a -> Type)) (b:Reln a) ->
    (forall x y. p x /\ b x y ==> p y)

private type m_rref (r:rid) (a:Type) (b:Reln a) = rref r a
 
val as_rref: #r:rid -> #a:Type -> #b:Reln a -> m_rref r a b -> GTot (rref r a)
let as_rref #r 'a 'b x = x

val as_ref: #r:rid -> #a:Type -> #b:Reln a -> m_rref r a b -> GTot (Heap.ref a)
let as_ref #r 'a 'b m = HyperHeap.as_ref m

type contains (#r:rid) (#a:Type) (#b:Reln a) (r:m_rref r a b) (m:t) =
  HyperHeap.contains_ref (as_rref r) m 

val sel: #r:rid -> #a:Type -> #b:Reln a -> h:t -> m_rref r a b -> GTot a
let sel #r (a:Type) (b:Reln a) h m = HyperHeap.sel h m

val upd: #r:rid -> #a:Type -> #b:Reln a -> h:t -> m_rref r a b -> a -> GTot t
let upd r 'a 'b h m v = HyperHeap.upd h m v

private type witnessed (#r:rid) (#a:Type) (#b:Reln a) (m:m_rref r a b) (p:(a -> Type)) = True

val ralloc: #a:Type
          -> #b:Reln a
	  -> r:rid
          -> init:a
          -> ST (m_rref r a b)
               (requires (fun _ -> monotonic a b))
	       (ensures (fun h0 (m:m_rref r a b) h1 -> ralloc_post r init h0 (as_rref m) h1))
let ralloc 'a 'b r init = ST.ralloc r init

val read:#r:rid 
       -> #a:Type
       -> #b:Reln a
       -> x:m_rref r a b
       -> ST a
            (requires (fun h -> True))
            (ensures (deref_post (as_rref x)))
let read #r 'a 'b x = !x

val write:#r:rid 
        -> #a:Type
        -> #b:Reln a
        -> x:m_rref r a b
        -> v:a
        -> ST unit
              (requires (fun h0 -> b (sel h0 x) v))
              (ensures (assign_post (as_rref x) v))
let write #r 'a 'b x v = x := v

val witness:#r:rid
          -> #a:Type
          -> #b:Reln a
          -> m:m_rref r a b
          -> p:(a -> Type)
          -> ST unit
                (requires (fun h0 -> p (sel h0 m) /\ stable p b))
                (ensures (fun h0 _ h1 -> h0=h1 /\ witnessed m p))
let witness #r (a:Type) (b:Reln a) m (p: a -> Type) = ()

assume val recall: #r:rid
		-> #a:Type
                -> #b:Reln a
                -> m:m_rref r a b
                -> p:(a -> Type)
                -> ST unit
                      (requires (fun _ ->  witnessed m p))
                      (ensures (fun h0 _ h1 -> h0=h1 /\ p (sel h1 m)))

