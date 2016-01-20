(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst
 --*)
module FStar.MRef
open FStar.Heap
open FStar.ST

kind Reln (a:Type) = a -> a -> Type

type monotonic (a:Type) (b:Reln a) =
  (forall x. b x x)                             (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

type stable : #a:Type -> (a -> Type) -> Reln a -> Type =
  fun (a:Type) (p:(a -> Type)) (b:Reln a) ->
    (forall x y. p x /\ b x y ==> p y)

private type mref (a:Type) (b:Reln a) = ref a

val as_ref: #a:Type -> #b:Reln a -> mref a b -> GTot (ref a)
let as_ref m = m

val contains: #a:Type -> #b:Reln a -> h:heap -> mref a b -> GTot bool
let contains h m = Heap.contains h (as_ref m)

val sel: #a:Type -> #b:Reln a -> h:heap -> mref a b -> GTot a
let sel (a:Type) (b:Reln a) h m = Heap.sel h (as_ref m)

val upd: #a:Type -> #b:Reln a -> h:heap -> mref a b -> a -> GTot heap
let upd h m v = Heap.upd h (as_ref m) v

private logic type token : #a:Type -> #b:Reln a -> mref a b -> (a -> Type) -> Type =
  fun (a:Type) (b:Reln a) (r:mref a b) (p:a -> Type) -> True

let fresh x h0 r h1 = not(contains h0 r) && contains h1 r && h1=upd h0 r x

val alloc: #a:Type
        -> #b:Reln a
        -> x:a{monotonic a b}
        -> ST (mref a b)
              (requires (fun _ -> True))
              (fun h0 r h1 -> b2t(fresh x h0 r h1))
let alloc x = ref x

val read: #a:Type
       -> #b:Reln a
       -> x:mref a b
       -> ST a
            (requires (fun h -> True))
            (ensures (fun h0 v h1 -> h0=h1 /\ v=sel h0 x))
let read x = !x

val write: #a:Type
        -> #b:Reln a
        -> x:mref a b
        -> v:a
        -> ST unit
              (requires (fun h0 -> b (sel h0 x) v))
              (ensures (fun h0 _ h1 -> h1=upd h0 x v))
let write x v = x := v

val witness: #a:Type
          -> #b:Reln a
          -> m:mref a b
          -> p:(a -> Type)
          -> ST unit
                (requires (fun h0 -> p (sel h0 m) /\ stable p b))
                (ensures (fun h0 _ h1 -> h0=h1 /\ token m p))
let witness (a:Type) (b:Reln a) m (p: a -> Type) = ()

assume val recall: #a:Type
                -> #b:Reln a
                -> m:mref a b
                -> p:(a -> Type)
                -> ST unit
                      (requires (fun _ ->  token m p))
                      (ensures (fun h0 _ h1 -> h0=h1 /\ p (sel h1 m)))
