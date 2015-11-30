(*--build-config
  options:--admit_fsi OrdSet;
  other-files:ordset.fsi
 --*)
module FStar.OrdMap

open FStar.OrdSet

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

type Equal (#k:Type) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) 

val eq_intro: #k:Type -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (forall x. select #k #v #f x m1 = select #k #v #f x m2))
                      (ensures (Equal m1 m2))
                 [SMTPatT (Equal m1 m2)]
  
val eq_lemma: #k:Type -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (Equal m1 m2))
                      (ensures (m1 = m2))
                 [SMTPatT (Equal m1 m2)]

val upd_order: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> y':v
               -> m:ordmap k v f
               -> Lemma (requires (x =!= x'))
                       (ensures (Equal (update #k #v #f x y (update #k #v #f x' y' m))
                                       (update #k #v #f x' y' (update #k #v #f x y m))))
                  [SMTPat (update #k #v #f x y (update #k #v #f x' y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates
                  
val upd_same_k: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> y':v
                -> m:ordmap k v f
                -> Lemma (requires (True))
                        (ensures (Equal (update #k #v #f x y (update #k #v #f x y' m))
					(update #k #v #f x y m)))
                   [SMTPat (update #k #v #f x y (update #k #v #f x y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates

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

val contains_upd1: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (contains #k #v #f x' (update #k #v #f x y m) =
                                      (x = x' || contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

val contains_upd2: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (x =!= x' ==> (contains #k #v #f x' (update #k #v #f x y m)
                                                    = contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

val contains_empty: #k:Type -> #v:Type -> #f:cmp k -> x:k
                    -> Lemma (requires True)
                             (ensures (not (contains #k #v #f x (empty #k #v #f))))
                       [SMTPat (contains #k #v #f x (empty #k #v #f))]

val contains_remove: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:k -> m:ordmap k v f
                     -> Lemma (requires True)
                              (ensures (contains #k #v #f x (remove #k #v #f y m) =
                                       (contains #k #v #f x m && not (x = y))))
                        [SMTPat (contains #k #v #f x (remove #k #v #f y m))]
                  
val eq_remove: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires (not (contains #k #v #f x m)))
                      (ensures (Equal m (remove #k #v #f x m)))
                 [SMTPat (remove #k #v #f x m)]

val choose_empty: #k:Type -> #v:Type -> #f:cmp k
                 -> Lemma (requires True) (ensures (is_None (choose #k #v #f
                                                             (empty #k #v #f))))
                    [SMTPat (choose #k #v #f (empty #k #v #f))]

val choose_m: #k:Type -> #v:Type -> #f:cmp k -> m:ordmap k v f
             -> Lemma (requires (~ (Equal m (empty #k #v #f))))
                     (ensures (is_Some (choose #k #v #f m) /\
                                (select #k #v #f (fst (Some.v (choose #k #v #f m))) m =
                                 Some (snd (Some.v (choose #k #v #f m)))) /\
                                (Equal m (update #k #v #f (fst (Some.v (choose #k #v #f m)))
                                                     (snd (Some.v (choose #k #v #f m)))
                                                     (remove #k #v #f (fst (Some.v (choose #k #v #f m))) m)))))
                [SMTPat (choose #k #v #f m)]

val size_empty: #k:Type -> #v:Type -> #f:cmp k
                -> Lemma (requires True)
                         (ensures (size #k #v #f (empty #k #v #f) = 0))
                   [SMTPat (size #k #v #f (empty #k #v #f))]
                   
val size_remove: #k:Type -> #v:Type -> #f:cmp k -> y:k -> m:ordmap k v f
                -> Lemma (requires (contains #k #v #f y m))
                         (ensures (size #k #v #f m = size #k #v #f (remove #k #v #f y m) + 1))
                   [SMTPat (size #k #v #f (remove #k #v #f y m))]

val dom_lemma: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
               -> Lemma (requires True)
                        (ensures (contains #k #v #f x m <==>
                                  OrdSet.mem #k #f x (dom #k #v #f m)))
                  [SMTPat (mem #k #f x (dom #k #v #f m))]

val contains_const_on: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                  -> Lemma (requires (True))
                           (ensures (mem y d = contains y (const_on d x)))
                                    //(contains y (const_on d x) ==> Some.v (select p w) = x)))
                     [SMTPat (contains #k #v #f y (const_on #k #v #f d x))]
                     
val select_const_on: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                     -> Lemma (requires (True))
                             (ensures (mem y d ==> (contains y (const_on d x) /\ Some.v (select y (const_on d x)) = x)))
                    [SMTPat (select #k #v #f y (const_on #k #v #f d x))]

val sel_rem1: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (OrdMap.remove #k #v #f x m) = None)
                 [SMTPat (select #k #v #f x (OrdMap.remove #k #v #f x m))]

val sel_rem2: #k:Type -> #v:Type -> #f:cmp k -> x:k -> x':k -> m:ordmap k v f
              -> Lemma (requires True) (ensures (x =!= x' ==>
                                                 select #k #v #f x'
                                                 (OrdMap.remove #k #v #f x m) = select #k #v #f x' m))
                 [SMTPat (select #k #v #f x' (OrdMap.remove #k #v #f x m))]

val rem_upd: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
             -> Lemma (requires (True)) (ensures (x =!= x' ==>
                                                  Equal (update #k #v #f x y (OrdMap.remove #k #v #f x' m)) 
                                                        (OrdMap.remove #k #v #f x' (update #k #v #f x y m))))
                [SMTPat (update #k #v #f x y (OrdMap.remove #k #v #f x' m))]
