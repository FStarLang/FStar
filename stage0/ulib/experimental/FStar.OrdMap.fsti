(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.OrdMap

open FStar.OrdSet

(* TODO (KM) : move me this should go in a common file on relations *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

let cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

val ordmap (k:eqtype) (v:Type u#a) (f:cmp k) : Type u#a

val empty   : #key:eqtype -> #value:Type -> #f:cmp key -> Tot (ordmap key value f)
val const_on: #key:eqtype -> #value:Type -> #f:cmp key -> d:ordset key f -> x:value -> Tot (ordmap key value f)
val select  : #key:eqtype -> #value:Type -> #f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
val update  : #key:eqtype -> #value:Type -> #f:cmp key -> key -> value
              -> m:ordmap key value f -> Tot (ordmap key value f)
val contains: #key:eqtype -> #value:Type -> #f:cmp key -> key -> ordmap key value f
              -> Tot bool
val dom     : #key:eqtype -> #value:Type -> #f:cmp key -> m:ordmap key value f ->
              Tot (ordset key f)

val remove  : #key:eqtype -> #value:Type -> #f:cmp key -> key
              -> ordmap key value f -> Tot (ordmap key value f)
val choose  : #key:eqtype -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot (option (key & value))

val size    : #key:eqtype -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot nat

val equal (#k:eqtype) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) : prop

val eq_intro: #k:eqtype -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (forall x. select #k #v #f x m1 == select #k #v #f x m2))
                      (ensures (equal m1 m2))
                 [SMTPat (equal m1 m2)]
  
val eq_lemma: #k:eqtype -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (equal m1 m2))
                      (ensures (m1 == m2))
                 [SMTPat (equal m1 m2)]

val upd_order: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> y':v
               -> m:ordmap k v f
               -> Lemma (requires (x =!= x'))
                       (ensures (equal (update #k #v #f x y (update #k #v #f x' y' m))
                                       (update #k #v #f x' y' (update #k #v #f x y m))))
                  [SMTPat (update #k #v #f x y (update #k #v #f x' y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates
                  
val upd_same_k: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> y':v
                -> m:ordmap k v f
                -> Lemma (requires (True))
                        (ensures (equal (update #k #v #f x y (update #k #v #f x y' m))
					(update #k #v #f x y m)))
                   [SMTPat (update #k #v #f x y (update #k #v #f x y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates

val sel_upd1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (update #k #v #f x y m) == Some y)
                 [SMTPat (select #k #v #f x (update #k #v #f x y m))]

val sel_upd2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
              -> Lemma (requires True)
                       (ensures (x =!= x' ==> (select #k #v #f x' (update #k #v #f x y m)
                                               == select #k #v #f x' m)))
                 [SMTPat (select #k #v #f x' (update #k #v #f x y m))]

val sel_empty: #k:eqtype -> #v:Type -> #f:cmp k -> x:k
               -> Lemma (requires True)
                        (ensures (select #k #v #f x (empty #k #v #f) == None))
                  [SMTPat (select #k #v #f x (empty #k #v #f))]

val sel_contains: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
                  -> Lemma (requires (True))
                           (ensures (contains #k #v #f x m = Some? (select #k #v #f x m)))
                     [SMTPat (select #k #v #f x m); SMTPat (contains #k #v #f x m)]

val contains_upd1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (contains #k #v #f x' (update #k #v #f x y m) =
                                      (x = x' || contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

val contains_upd2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (x =!= x' ==> (contains #k #v #f x' (update #k #v #f x y m)
                                                    = contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

val contains_empty: #k:eqtype -> #v:Type -> #f:cmp k -> x:k
                    -> Lemma (requires True)
                             (ensures (not (contains #k #v #f x (empty #k #v #f))))
                       [SMTPat (contains #k #v #f x (empty #k #v #f))]

val contains_remove: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:k -> m:ordmap k v f
                     -> Lemma (requires True)
                              (ensures (contains #k #v #f x (remove #k #v #f y m) =
                                       (contains #k #v #f x m && not (x = y))))
                        [SMTPat (contains #k #v #f x (remove #k #v #f y m))]
                  
val eq_remove: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires (not (contains #k #v #f x m)))
                      (ensures (equal m (remove #k #v #f x m)))
                 [SMTPat (remove #k #v #f x m)]

val choose_empty: #k:eqtype -> #v:Type -> #f:cmp k
                 -> Lemma (requires True) (ensures (None? (choose #k #v #f
                                                             (empty #k #v #f))))
                    [SMTPat (choose #k #v #f (empty #k #v #f))]

val choose_m: #k:eqtype -> #v:Type -> #f:cmp k -> m:ordmap k v f
             -> Lemma (requires (~ (equal m (empty #k #v #f))))
                     (ensures (Some? (choose #k #v #f m) /\
                                (select #k #v #f (fst (Some?.v (choose #k #v #f m))) m ==
                                 Some (snd (Some?.v (choose #k #v #f m)))) /\
                                (equal m (update #k #v #f (fst (Some?.v (choose #k #v #f m)))
                                                     (snd (Some?.v (choose #k #v #f m)))
                                                     (remove #k #v #f (fst (Some?.v (choose #k #v #f m))) m)))))
                [SMTPat (choose #k #v #f m)]

val size_empty: #k:eqtype -> #v:Type -> #f:cmp k
                -> Lemma (requires True)
                         (ensures (size #k #v #f (empty #k #v #f) = 0))
                   [SMTPat (size #k #v #f (empty #k #v #f))]
                   
val size_remove: #k:eqtype -> #v:Type -> #f:cmp k -> y:k -> m:ordmap k v f
                -> Lemma (requires (contains #k #v #f y m))
                         (ensures (size #k #v #f m = size #k #v #f (remove #k #v #f y m) + 1))
                   [SMTPat (size #k #v #f (remove #k #v #f y m))]

val dom_lemma: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
               -> Lemma (requires True)
                        (ensures (contains #k #v #f x m <==>
                                  OrdSet.mem #k #f x (dom #k #v #f m)))
                  [SMTPat (mem #k #f x (dom #k #v #f m))]

val contains_const_on: #k:eqtype -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                  -> Lemma (requires (True))
                           (ensures (mem y d = contains y (const_on d x)))
                                    //(contains y (const_on d x) ==> Some?.v (select p w) = x)))
                     [SMTPat (contains #k #v #f y (const_on #k #v #f d x))]
                     
val select_const_on: #k:eqtype -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                     -> Lemma (requires True)
                             (ensures (mem y d ==> (contains y (const_on d x) /\ Some?.v (select y (const_on d x)) == x)))
                    [SMTPat (select #k #v #f y (const_on #k #v #f d x))]

val sel_rem1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (remove #k #v #f x m) == None)
                 [SMTPat (select #k #v #f x (remove #k #v #f x m))]

val sel_rem2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> x':k -> m:ordmap k v f
              -> Lemma (requires True) (ensures (x =!= x' ==>
                                                 select #k #v #f x'
                                                 (remove #k #v #f x m) == select #k #v #f x' m))
                 [SMTPat (select #k #v #f x' (remove #k #v #f x m))]

val rem_upd: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
             -> Lemma (requires (True)) (ensures (x =!= x' ==>
                                                  equal (update #k #v #f x y (remove #k #v #f x' m))
                                                        (remove #k #v #f x' (update #k #v #f x y m))))
                [SMTPat (update #k #v #f x y (remove #k #v #f x' m))]
