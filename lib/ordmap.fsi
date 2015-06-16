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

val empty   : #key:Type -> #value:Type -> #f:cmp key -> Tot (ordmap key value f)
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

val eq_lemma: #k:Type -> #v:Type -> f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (Equal #k #v #f m1 m2))
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

val update_lem: #key:Type -> #value:Type -> f:cmp key -> k:key -> v:value -> k':key
                -> m:ordmap key value f
                -> Lemma (requires True)
                         (ensures ((k = k'       ==> (select f k' (update f k v m) = Some v)) /\
                                  ((not (k = k') ==> (select f k' (update f k v m) = select f k' m)))))
                   [SMTPat (select f k' (update f k v m))]
                   
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
                  [SMTPat (dom f (empty f))]

val choose_lem: #key:Type -> #value:Type -> f:cmp key -> m:ordmap key value f
  -> Lemma (requires True)
           (ensures ((m = empty f       ==> (choose f m = None)) /\
                     (not (m = empty f) ==> ((is_Some (choose f m)) /\
                                             (select f (fst (Some.v (choose f m))) m =
                                                    Some (snd (Some.v (choose f m)))) /\
                                             (m = update f (fst (Some.v (choose f m)))
                                                           (snd (Some.v (choose f m)))
                                                           (remove f (fst (Some.v (choose f m))) m))))))
           [SMTPat (choose f m)]
                                                                        
val size_remove_lem: #key:Type -> #value:Type -> f:cmp key -> k:key
                     -> m:ordmap key value f
                     -> Lemma (requires (contains f k m))
                              (ensures (size f m = 1 + size f (remove f k m)))
                        [SMTPat (size f (remove f k m))]
                                                             