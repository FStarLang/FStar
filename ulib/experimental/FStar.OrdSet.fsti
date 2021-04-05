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
module FStar.OrdSet

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
   (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)  (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)   (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                 (* totality      *)

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

let rec sorted (#a:eqtype) (f:cmp a) (l:list a) : Tot bool =
  match l with
  | []       -> true
  | x::[]    -> true
  | x::y::tl -> f x y && x <> y && sorted f (y::tl)

val ordset (a:eqtype) (f:cmp a) : Type0

val hasEq_ordset: a:eqtype -> f:cmp a
  -> Lemma (requires (True)) (ensures (hasEq (ordset a f)))
    [SMTPat (hasEq (ordset a f))]

private val as_list (#a:eqtype) (#f:cmp a) (s:ordset a f) : Tot (l:list a{sorted f l})

val empty        : #a:eqtype -> #f:cmp a -> Tot (ordset a f)
val mem          : #a:eqtype -> #f:cmp a -> a -> s:ordset a f -> Tot bool

val union        : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
val intersect    : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

val choose       : #a:eqtype -> #f:cmp a -> s:ordset a f -> Tot (option a)
val remove       : #a:eqtype -> #f:cmp a -> a -> ordset a f -> Tot (ordset a f)

val size         : #a:eqtype -> #f:cmp a -> ordset a f -> Tot nat

val subset       : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
val singleton    : #a:eqtype -> #f:cmp a -> a -> Tot (ordset a f)

val minus        : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
val strict_subset: #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool

let disjoint #a #f (s1 s2 : ordset a f) : Tot bool = intersect s1 s2 = empty

let equal (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) : Tot prop =
  forall x. mem #_ #f x s1 = mem #_ #f x s2

val eq_lemma: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
              -> Lemma (requires (equal s1 s2))
                       (ensures (s1 = s2))
                 [SMTPat (equal s1 s2)]

val mem_empty: #a:eqtype -> #f:cmp a -> x:a
               -> Lemma (requires True) (ensures (not (mem #a #f x (empty #a #f))))
                  [SMTPat (mem #a #f x (empty #a #f))]

val mem_singleton: #a:eqtype -> #f:cmp a -> x:a -> y:a
                   -> Lemma (requires True)
                            (ensures (mem #a #f y (singleton #a #f x)) = (x = y))
                      [SMTPat (mem #a #f y (singleton #a #f x))]

val mem_union: #a:eqtype -> #f:cmp a -> x:a -> s1:ordset a f -> s2:ordset a f
               -> Lemma (requires True)
                        (ensures (mem #a #f x (union #a #f s1 s2) =
                                  (mem #a #f x s1 || mem #a #f x s2)))
                  [SMTPat (mem #a #f x (union #a #f s1 s2))]

val mem_intersect: #a:eqtype -> #f:cmp a -> x:a -> s1:ordset a f -> s2:ordset a f
                   -> Lemma (requires True)
                            (ensures (mem #a #f x (intersect s1 s2) =
                                      (mem #a #f x s1 && mem #a #f x s2)))
                      [SMTPat (mem #a #f x (intersect #a #f s1 s2))]

val mem_subset: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures  (subset #a #f s1 s2 <==>
                                    (forall x. mem #a #f x s1 ==> mem #a #f x s2)))
                   [SMTPat (subset #a #f s1 s2)]

val choose_empty: #a:eqtype -> #f:cmp a
                  -> Lemma (requires True) (ensures (None? (choose #a #f (empty #a #f))))
                     [SMTPat (choose #a #f (empty #a #f))]

(* TODO: FIXME: Pattern does not contain all quantified vars *)
val choose_s: #a:eqtype -> #f:cmp a -> s:ordset a f
              -> Lemma (requires (not (s = (empty #a #f))))
                       (ensures (Some? (choose #a #f s) /\
                                 s = union #a #f (singleton #a #f (Some?.v (choose #a #f s)))
                                                 (remove #a #f (Some?.v (choose #a #f s)) s)))
                 [SMTPat (choose #a #f s)]

val mem_remove: #a:eqtype -> #f:cmp a -> x:a -> y:a -> s:ordset a f
                -> Lemma (requires True)
                         (ensures (mem #a #f x (remove #a #f y s) =
                                   (mem #a #f x s && not (x = y))))
                   [SMTPat (mem #a #f x (remove #a #f y s))]

val eq_remove: #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (not (mem #a #f x s)))
                        (ensures (s = remove #a #f x s))
                  [SMTPat (remove #a #f x s)]

val size_empty: #a:eqtype -> #f:cmp a -> s:ordset a f
                -> Lemma (requires True) (ensures ((size #a #f s = 0) = (s = empty #a #f)))
                  [SMTPat (size #a #f s)]

val size_remove: #a:eqtype -> #f:cmp a -> y:a -> s:ordset a f
                 -> Lemma (requires (mem #a #f y s))
                          (ensures (size #a #f s = size #a #f (remove #a #f y s) + 1))
                    [SMTPat (size #a #f (remove #a #f y s))]

val size_singleton: #a:eqtype -> #f:cmp a -> x:a
                    -> Lemma (requires True) (ensures (size #a #f (singleton #a #f x) = 1))
                       [SMTPat (size #a #f (singleton #a #f x))]

val subset_size: #a:eqtype -> #f:cmp a -> x:ordset a f -> y:ordset a f
                 -> Lemma (requires (subset #a #f x y))
 	                  (ensures (size #a #f x <= size #a #f y))
	           [SMTPat (subset #a #f x y)]

(**********)

val size_union: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures ((size #a #f (union #a #f s1 s2) >= size #a #f s1) &&
                                   (size #a #f (union #a #f s1 s2) >= size #a #f s2)))
                         [SMTPat (size #a #f (union #a #f s1 s2))]

(**********)

val fold (#a:eqtype) (#acc:Type) (#f:cmp a) (g:acc -> a -> acc) (init:acc) (s:ordset a f)
  : Tot acc

val map (#a #b:eqtype) (#fa:cmp a) (#fb:cmp b) (g:a -> b) (sa:ordset a fa)
  : Pure (ordset b fb)
    (requires (forall x y. x `fa` y ==> g x `fb` g y))
    (ensures (fun sb -> True))

val lemma_strict_subset_size (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  :Lemma (requires (strict_subset s1 s2))
         (ensures  (subset s1 s2 /\ size s1 < size s2))
   [SMTPat (strict_subset s1 s2)]

val lemma_minus_mem (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (x:a)
  :Lemma (requires True) (ensures (mem x (minus s1 s2) = (mem x s1 && not (mem x s2))))
   [SMTPat (mem x (minus s1 s2))]

val lemma_strict_subset_minus_size (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s:ordset a f)
  :Lemma (requires (strict_subset s1 s2 /\ subset s1 s /\ subset s2 s))
         (ensures  (size (minus s s2) < size (minus s s1)))
   [SMTPat (strict_subset s1 s2); SMTPat (subset s1 s); SMTPat (subset s2 s)]

val lemma_disjoint_union_subset (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  :Lemma (requires (~ (s1 == empty) /\ ~ (s2 == empty) /\ intersect s1 s2 == empty))
         (ensures  (strict_subset s1 (union s1 s2) /\ strict_subset s2 (union s1 s2)))
   [SMTPatOr [[SMTPat (strict_subset s1 (union s1 s2))]; [SMTPat (strict_subset s2 (union s1 s2))]]]

val lemma_subset_union (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s:ordset a f)
  :Lemma (requires (subset s1 s /\ subset s2 s))
         (ensures  (subset (union s1 s2) s))
   [SMTPat (subset (union s1 s2) s)]

val lemma_strict_subset_transitive (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  :Lemma (requires (strict_subset s1 s2 /\ strict_subset s2 s3))
         (ensures  (strict_subset s1 s3))
   [SMTPat (strict_subset s1 s2); SMTPat (strict_subset s2 s3)]

val lemma_intersect_symmetric (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  :Lemma (requires True) (ensures (intersect s1 s2 == intersect s2 s1))
   [SMTPatOr [[SMTPat (intersect s1 s2)]; [SMTPat (intersect s2 s1)]]]

val lemma_intersect_union_empty (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  :Lemma (requires (intersect s1 s3 == empty /\ intersect s2 s3 == empty))
         (ensures  (intersect (union s1 s2) s3 == empty))
   [SMTPat (intersect (union s1 s2) s3)]

val lemma_intersect_union_empty' (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  :Lemma (requires (intersect (union s1 s2) s3 == empty))
         (ensures  (intersect s1 s3 == empty /\ intersect s2 s3 == empty))
   [SMTPat (intersect (union s1 s2) s3)]

val union_comm (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  :Lemma (union s1 s2 == union s2 s1)
         [SMTPat (union s1 s2)]

val union_of_disj (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
 :Lemma (requires (disjoint s1 s2))
        (ensures (minus (union s1 s2) s1 == s2))
        [SMTPat (union s1 s2); SMTPat (disjoint s1 s2)]

(* Conversion from OrdSet to Set *)

module S = FStar.Set

val as_set : #a:eqtype -> #f:cmp a -> ordset a f -> Tot (S.set a)

val lemma_as_set_mem (#a:eqtype) (#f:cmp a) (s:ordset a f) (x:a)
  : Lemma (mem x s <==> S.mem x (as_set s))
          [SMTPat (mem x s);
           SMTPat (S.mem x (as_set s))]

val lemma_as_set_disjoint (#a:eqtype) (#f:cmp a) (s1 s2:ordset a f)
  : Lemma (intersect s1 s2 = empty <==> S.disjoint (as_set s1) (as_set s2))
          [SMTPat (S.disjoint (as_set s1) (as_set s2))]
