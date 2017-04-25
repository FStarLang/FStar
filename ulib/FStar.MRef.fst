module FStar.MRef
open FStar.Heap
open FStar.ST

let reln (a:Type) = a -> a -> Type

let monotonic (a:Type) (b:reln a) =
  (forall x. b x x)                             (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

abstract let mref (a:Type) (b:reln a) = ref a
val as_ref: #a:Type -> #b:reln a -> mref a b -> GTot (ref a)
let as_ref #a #b m = m

let contains (#a:Type) (#b:reln a) (h:heap) (m:mref a b) = Heap.contains h (as_ref m)

val sel: #a:Type -> #b:reln a -> h:heap -> mref a b -> GTot a
let sel #a #b h m = Heap.sel h (as_ref m)

val upd: #a:Type -> #b:reln a -> h:heap -> mref a b -> a -> GTot heap
let upd #a #b h m v = Heap.upd h (as_ref m) v

abstract type token (#a:Type) (#b:reln a) (r:mref a b) (p:a -> Type) = True
abstract type witnessed (p:heap -> Type) = True

type fresh(#a:Type) (#b:reln a) (x:a) h0 (r:mref a b) h1 = 
  ~ (contains h0 r) /\ contains h1 r /\ h1==upd h0 r x

val alloc: #a:Type
        -> #b:reln a
        -> x:a{monotonic a b}
        -> ST (mref a b)
              (requires (fun _ -> True))
              (fun h0 r h1 -> fresh x h0 r h1)
let alloc #a #b x = ST.alloc x

val read: #a:Type
       -> #b:reln a
       -> x:mref a b
       -> ST a
            (requires (fun h -> True))
            (ensures (fun h0 v h1 -> h0==h1 /\ v==sel h0 x))
let read #a #b x = !x

val write: #a:Type
        -> #b:reln a
        -> x:mref a b
        -> v:a
        -> ST unit
              (requires (fun h0 -> b (sel h0 x) v))
              (ensures (fun h0 _ h1 -> h1==upd h0 x v))
let write #a #b x v = x := v

let stable (#a:Type) (p:(a -> Type)) (b:reln a) = forall x y. p x /\ b x y ==> p y
val take_token: #a:Type
          -> #b:reln a
          -> m:mref a b
          -> p:(a -> Type)
          -> ST unit
                (requires (fun h0 -> p (sel h0 m) /\ stable p b))
                (ensures (fun h0 _ h1 -> h0==h1 /\ token m p))
let take_token #a #b m p = ()
assume val recall_token: #a:Type
                     -> #b:reln a
                     -> m:mref a b
                     -> p:(a -> Type)
                     -> ST unit
                       (requires (fun _ ->  token m p))
                       (ensures (fun h0 _ h1 -> h0==h1 /\ p (sel h1 m)))

let stable_on_heap (#a:Type) (#b:reln a) (r:mref a b) (p:(heap -> Type)) = 
  forall h0 h1. p h0 /\ b (sel h0 r) (sel h1 r) ==> p h1
  
assume val recall: p:(heap -> Type)
                -> ST unit
                      (requires (fun _ ->  witnessed p))
                      (ensures (fun h0 _ h1 -> p h1))

val witness: #a:Type
          -> #b:reln a
          -> m:mref a b
          -> p:(heap -> Type)
          -> ST unit
                (requires (fun h0 -> p h0 /\ stable_on_heap m p))
                (ensures (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness #a #b m p = ()
