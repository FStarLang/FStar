(*--Build-config

 --*)
module FStar.OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

type ordset : a:Type -> cmp a -> Type

val empty     : #a:Type -> #f:cmp a -> Tot (ordset a f)
val union     : #a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
val intersect : #a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

val mem       : #a:Type -> #f:cmp a -> a -> s:ordset a f -> Tot bool
val choose    : #a:Type -> #f:cmp a -> s:ordset a f -> Tot (option a)
val remove    : #a:Type -> #f:cmp a -> a -> ordset a f -> Tot (ordset a f)

val size      : #a:Type -> #f:cmp a -> ordset a f -> Tot nat

val subset    : #a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
val singleton : #a:Type -> #f:cmp a -> a -> Tot (ordset a f)

opaque type Equal (#a:Type) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) =
  (forall x. mem x s1 = mem x s2)

val eq_lemma: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
              -> Lemma (requires (Equal s1 s2))
                       (ensures (s1 = s2))
                 [SMTPatT (Equal s1 s2)]

val mem_empty: #a:Type -> #f:cmp a -> x:a
               -> Lemma (requires True) (ensures (not (mem #a #f x (empty #a #f))))
                  [SMTPat (mem #a #f x (empty #a #f))]

val mem_singleton: #a:Type -> #f:cmp a -> x:a -> y:a
                   -> Lemma (requires True)
                            (ensures (mem #a #f y (singleton #a #f x)) = (x = y))
                      [SMTPat (mem #a #f y (singleton #a #f x))]

val mem_union: #a:Type -> #f:cmp a -> x:a -> s1:ordset a f -> s2:ordset a f
               -> Lemma (requires True)
                        (ensures (mem #a #f x (union #a #f s1 s2) =
                                  (mem #a #f x s1 || mem #a #f x s2)))
                  [SMTPat (mem #a #f x (union #a #f s1 s2))]

val mem_intersect: #a:Type -> #f:cmp a -> x:a -> s1:ordset a f -> s2:ordset a f
                   -> Lemma (requires True)
                            (ensures (mem #a #f x (intersect s1 s2) =
                                      (mem #a #f x s1 && mem #a #f x s2)))
                      [SMTPat (mem #a #f x (intersect #a #f s1 s2))]

val mem_subset: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures  (subset #a #f s1 s2 <==>
                                    (forall x. mem #a #f x s1 ==> mem #a #f x s2)))
                   [SMTPat (subset #a #f s1 s2)]

val choose_empty: #a:Type -> #f:cmp a
                  -> Lemma (requires True) (ensures (is_None (choose #a #f (empty #a #f))))
                     [SMTPat (choose #a #f (empty #a #f))]

(* TODO: FIXME: Pattern does not contain all quantified vars *)
val choose_s: #a:Type -> #f:cmp a -> s:ordset a f
              -> Lemma (requires (not (s = (empty #a #f))))
                       (ensures (is_Some (choose #a #f s) /\
                                 s = union #a #f (singleton #a #f (Some.v (choose #a #f s)))
                                                 (remove #a #f (Some.v (choose #a #f s)) s)))
                 [SMTPat (choose #a #f s)]

val mem_remove: #a:Type -> #f:cmp a -> x:a -> y:a -> s:ordset a f
                -> Lemma (requires True)
                         (ensures (mem #a #f x (remove #a #f y s) =
                                   (mem #a #f x s && not (x = y))))
                   [SMTPat (mem #a #f x (remove #a #f y s))]

val eq_remove: #a:Type -> #f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (not (mem #a #f x s)))
                        (ensures (s = remove #a #f x s))
                  [SMTPat (remove #a #f x s)]

val size_empty: #a:Type -> #f:cmp a -> s:ordset a f
                -> Lemma (requires True) (ensures ((size #a #f s = 0) = (s = empty #a #f)))
                  [SMTPat (size #a #f s)]
                   
val size_remove: #a:Type -> #f:cmp a -> y:a -> s:ordset a f
                 -> Lemma (requires (mem #a #f y s))
                          (ensures (size #a #f s = size #a #f (remove #a #f y s) + 1))
                    [SMTPat (size #a #f (remove #a #f y s))]

val size_singleton: #a:Type -> #f:cmp a -> x:a
                    -> Lemma (requires True) (ensures (size #a #f (singleton #a #f x) = 1))
                       [SMTPat (size #a #f (singleton #a #f x))]
                       
(* TODO:FIXME: implement *)
val size_union: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures ((size #a #f (union #a #f s1 s2) >= size #a #f s1) &&
                                   (size #a #f (union #a #f s1 s2) >= size #a #f s2)))
                         [SMTPat (size #a #f (union #a #f s1 s2))]

val subset_size: #a:Type -> #f:cmp a -> x:ordset a f -> y:ordset a f
                 -> Lemma (requires (subset #a #f x y))
	                 (ensures (size #a #f x <= size #a #f y))
	           [SMTPat (subset #a #f x y)]
