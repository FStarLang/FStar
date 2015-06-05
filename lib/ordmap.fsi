(*--build-config

 --*)
module OrdMap

open OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

type ordmap: key:Type -> value:Type -> cmp key -> Type

val empty:  #key:Type -> #value:Type -> f:cmp key -> Tot (ordmap key value f)

val contains: #key:Type -> #value:Type -> f:cmp key -> key -> ordmap key value f
              -> Tot bool
val select  : #key:Type -> #value:Type -> f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
val update  : #key:Type -> #value:Type -> f:cmp key -> key -> value
              -> m:ordmap key value f -> Tot (ordmap key value f)
val dom     : #key:Type -> #value:Type -> f:cmp key -> m:ordmap key value f ->
              Tot (ordset key f)

val remove  : #key:Type -> #value:Type -> f:cmp key -> key
              -> ordmap key value f -> Tot (ordmap key value f)
val choose  : #key:Type -> #value:Type -> f:cmp key -> ordmap key value f
              -> Tot (option (key * value))
                       
val eq_lemma: #key:Type -> #value:Type -> f:cmp key
              -> m1:ordmap key value f -> m2:ordmap key value f
              -> Lemma (requires (forall x. select f x m1 = select f x m2))
                       (ensures (m1 = m2))

val empty_lem: #key:Type -> #value:Type -> f:cmp key
               -> Lemma (requires True) (ensures (forall k. not (contains f k (empty #key #value f))))
                  [SMTPat (empty f)]

val contains_lem: #key:Type -> #value:Type -> f:cmp key -> m:ordmap key value f
                  -> Lemma (requires True) (ensures (forall k. contains f k m =
                                                               mem f k (dom f m)))
                     [SMTPat (dom f m)]

val select_lem: #key:Type -> #value:Type -> f:cmp key -> k:key
                -> m:ordmap key value f
                -> Lemma (requires True)
                         (ensures (is_Some (select f k m) = contains f k m))
                   [SMTPat (select f k m); SMTPat (contains f k m)]

val update_lem: #key:Type -> #value:Type -> f:cmp key -> k:key -> v:value
                -> m:ordmap key value f
                -> Lemma (requires True)
                         (ensures (select f k (update f k v m) = Some v /\
                                   (forall k'. k =!= k' ==> (select f k' (update f k v m) = select f k' m))))
                   [SMTPat (select f k (update f k v m))]
                   
val remove_lem: #key:Type -> #value:Type -> f:cmp key -> k:key
                -> m:ordmap key value f
                -> Lemma (requires True)
                         (ensures (select f k (remove f k m) = None /\
                                   (forall k'. k =!= k' ==> (select f k' (remove f k m) = select f k' m))))
                   [SMTPat (select f k (remove f k m))]

val dom_empty: #key:Type -> #value:Type -> f:cmp key
               -> m:ordmap key value f
               -> Lemma (requires True)
                        (ensures ((dom f m = OrdSet.empty f) <==> (m = empty f)))

val choose_lem: #key:Type -> #value:Type -> f:cmp key -> m:ordmap key value f
  -> Lemma (requires True)
           (ensures ((dom f m = OrdSet.empty f       ==> (choose f m = None)) /\
                     (not (dom f m = OrdSet.empty f) ==> (is_Some (choose f m) /\
                                                          (select f (fst (Some.v (choose f m))) m =
                                                                Some (snd (Some.v (choose f m)))) /\
                                                          (m = update f (fst (Some.v (choose f m)))
                                                                        (snd (Some.v (choose f m)))
                                                                        (remove f (fst (Some.v (choose f m))) m))))))
                                                             