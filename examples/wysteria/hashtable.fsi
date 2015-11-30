(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst
 --*)
module Hashtable

type t : Type -> Type -> Type

val create: a:Type -> b:Type -> n:nat -> Tot (t a b)

val find: #a:Type -> #b:Type -> t a b -> a -> b

val mem: #a:Type -> #b:Type -> t a b -> a -> Tot bool

val add: #a:Type -> #b:Type -> t a b -> a -> b -> Tot (t a b)
