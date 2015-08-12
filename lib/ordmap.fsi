(*--build-config
  options:--admit_fsi OrdSet;
  other-files:ordset.fsi
 --*)
module OrdMap

open OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

type ordmap: key:Type -> value:Type -> cmp key -> Type

val empty   : #key:Type -> #value:Type -> #f:cmp key -> Tot (ordmap key value f)
val const_on: #key:Type -> #value:Type -> #f:cmp key -> d:ordset key f -> x:value -> Tot (ordmap key value f)
val select  : #key:Type -> #value:Type -> #f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
val update  : #key:Type -> #value:Type -> #f:cmp key -> key -> value
              -> m:ordmap key value f -> Tot (ordmap key value f)
val contains: #key:Type -> #value:Type -> #f:cmp key -> key -> ordmap key value f
              -> Tot bool
val dom     : #key:Type -> #value:Type -> #f:cmp key -> m:ordmap key value f ->
              Tot (ordset key f)

val remove  : #key:Type -> #value:Type -> #f:cmp key -> key
              -> ordmap key value f -> Tot (ordmap key value f)
val choose  : #key:Type -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot (option (key * value))

val size    : #key:Type -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot nat

type Equal (#k:Type) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) =
  (forall x. select #k #v #f x m1 = select #k #v #f x m2)

val eq_lemma: #k:Type -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (forall x. select #k #v #f x m1 = select #k #v #f x m2))
                       (ensures (m1 = m2))
                 [SMTPat (m1 = m2)]

val upd_order: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> y':v
               -> m:ordmap k v f
               -> Lemma (requires (x =!= x'))
                        (ensures (update #k #v #f x y (update #k #v #f x' y' m) =
                                  update #k #v #f x' y' (update #k #v #f x y m)))
                  [SMTPat (update #k #v #f x y (update #k #v #f x' y' m))]
                  
val upd_same_k: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> y':v
                -> m:ordmap k v f
                -> Lemma (requires (True))
                         (ensures (update #k #v #f x y (update #k #v #f x y' m) =
                                   update #k #v #f x y m))
                   [SMTPat (update #k #v #f x y (update #k #v #f x y' m))]

val sel_upd1: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (update #k #v #f x y m) = Some y)
                 [SMTPat (select #k #v #f x (update #k #v #f x y m))]

val sel_upd2: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
              -> Lemma (requires True)
                       (ensures (x =!= x' ==> (select #k #v #f x' (update #k #v #f x y m)
                                               = select #k #v #f x' m)))
                 [SMTPat (select #k #v #f x' (update #k #v #f x y m))]

val sel_empty: #k:Type -> #v:Type -> #f:cmp k -> x:k
               -> Lemma (requires True)
                        (ensures (select #k #v #f x (empty #k #v #f) = None))
                  [SMTPat (select #k #v #f x (empty #k #v #f))]
                  
val sel_contains: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
                  -> Lemma (requires (True))
                           (ensures (contains #k #v #f x m = is_Some (select #k #v #f x m)))
                     [SMTPat (select #k #v #f x m); SMTPat (contains #k #v #f x m)]

