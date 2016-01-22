(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
 --*)
module Hashtable

type t : Type -> Type -> Type

val create: a:Type -> b:Type -> n:nat -> Tot (t a b)

val find: #a:Type -> #b:Type -> t a b -> a -> b

val mem: #a:Type -> #b:Type -> t a b -> a -> Tot bool

val add: #a:Type -> #b:Type -> t a b -> a -> b -> Tot (t a b)
