(*--build-config

 --*)
module OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

type ordset : a:Type -> cmp a -> Type

val empty     : #a:Type -> f:cmp a -> Tot (ordset a f)
val insert    : #a:Type -> f:cmp a -> a -> ordset a f -> Tot (ordset a f)
val union     : #a:Type -> f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
val intersect : #a:Type -> f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

val mem       : #a:Type -> f:cmp a -> a -> ordset a f -> Tot bool
val choose    : #a:Type -> f:cmp a -> s:ordset a f -> Tot (option a)
val remove    : #a:Type -> f:cmp a -> a -> ordset a f -> Tot (ordset a f)

val size      : #a:Type -> f:cmp a -> ordset a f -> Tot nat

val subset    : #a:Type -> f:cmp a -> ordset a f -> ordset a f -> Tot bool
//val singleton : #a:Type -> f:cmp a -> a -> Tot (s:ordset a f{size f s = 1})
val singleton : #a:Type -> f:cmp a -> a -> Tot (ordset a f)

val is_singleton: #a:Type -> f:cmp a -> ordset a f -> Tot bool



type Equal (#a:Type) (f:cmp a) (s1:ordset a f) (s2:ordset a f) =
  (forall x. mem f x s1 = mem f x s2)

val eq_lemma: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f
              -> Lemma (requires (Equal f s1 s2))
                       (ensures s1 = s2)
                       [SMTPat (s1 = s2)]

val mem_empty: #a:Type -> f:cmp a
               -> Lemma (requires True) (ensures (forall x. not (mem f x (empty f))))
                  [SMTPat (empty f)]

val insert_lem: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                -> Lemma (requires True)
                         (ensures ((mem f x s       ==> (s = insert f x s)) /\
                                   (not (mem f x s) ==> ((forall y. mem f y s ==> mem f y (insert f x s)) /\
                                                         (forall y. mem f y (insert f x s) = (y = x || mem f y s))))))
                   [SMTPat (insert f x s)]
                   
val mem_union: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
               -> Lemma (requires True)            
                        (ensures (mem f x (union f s1 s2) = (mem f x s1 || mem f x s2)))
                        [SMTPat (mem f x (union f s1 s2))]

val mem_intersect: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
                   -> Lemma (requires True)
                            (ensures (mem f x (intersect f s1 s2) = (mem f x s1 && mem f x s2)))
                            [SMTPat (mem f x (intersect f s1 s2))]

val choose_lem: #a:Type -> f:cmp a -> s:ordset a f
                -> Lemma (requires True)
                   (ensures ((s = empty f       ==> is_None (choose f s)) /\
                             (not (s = empty f) ==> (is_Some (choose f s) /\
                                                     s = insert f (Some.v (choose f s)) (remove f (Some.v (choose f s)) s)))))
                   [SMTPat (choose f s)]

val remove_lem: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                -> Lemma (requires True)
                   (ensures ((not (mem f x s) ==> (s = remove f x s)) /\
                             (mem f x s       ==> ((not (mem f x (remove f x s))) /\
                                                   (forall y. mem f y s = (x = y || mem f y (remove f x s))) /\
                                                   (forall y. mem f y (remove f x s) ==> mem f y s)))))
                   [SMTPat (remove f x s)]
                  
val remove_size: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                 -> Lemma (requires (mem f x s))
                          (ensures (size f s = size f (remove f x s) + 1))
                    [SMTPat (size f (remove f x s))]
                    
val mem_subset: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires (True))
                         (ensures  (subset f s1 s2 <==> (forall x. mem f x s1 ==> mem f x s2)))
                   [SMTPat (subset f s1 s2)]
                   
val mem_singleton: #a:Type -> f:cmp a -> x:a -> y:a
                   -> Lemma (requires (True))
                            (ensures (mem f y (singleton f x) <==> x = y))
                      [SMTPat (mem f y (singleton f x))]
                      
val is_singleton_lemma: #a:Type -> f:cmp a -> x:a
                        -> Lemma (requires (True))
                                 (ensures  (is_singleton f (singleton f x) = true))
                           [SMTPat (is_singleton f (singleton f x))]

                    
(**********)
