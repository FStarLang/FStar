(*--build-config

 --*)
module OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality *)


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

val eq_lemma: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f
              -> Lemma (requires (forall x. mem f x s1 = mem f x s2))
                       (ensures s1 = s2)

val mem_empty: #a:Type -> f:cmp a -> x:a
               -> Lemma (requires True) (ensures (not (mem f x (empty f))))
                  [SMTPat (mem f x (empty f))]

val mem_insert: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                -> Lemma (requires True)
                         (ensures (mem f x (insert f x s)))
                   [SMTPat (mem f x (insert f x s))]
                   
val mem_insert_all: #a:Type -> f:cmp a -> x:a -> s:ordset a f -> y:a
                    -> Lemma (requires (True))
                             (ensures (mem f y (insert f x s) = (y = x || mem f y s)))
                  
val mem_union: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
               -> Lemma (requires True)            
                        (ensures (mem f x (union f s1 s2) = (mem f x s1 || mem f x s2)))
                        [SMTPat (mem f x (union f s1 s2))]

val mem_intersect: #a:Type -> f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
                   -> Lemma (requires True)
                            (ensures (mem f x (intersect f s1 s2) = (mem f x s1 && mem f x s2)))
                            [SMTPat (mem f x (intersect f s1 s2))]

val mem_choose: #a:Type -> f:cmp a -> s:ordset a f
                -> Lemma (requires True) (ensures ((is_Some (choose f s) ==> mem f (Some.v (choose f s)) s) /\
                                                   (is_None (choose f s) ==> s = empty f)))
                   [SMTPat (choose f s)]

val mem_remove: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                -> Lemma (requires True) (ensures (not (mem f x (remove f x s))))
                   [SMTPat (mem f x (remove f x s))]

(**********)