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

val empty        : #a:eqtype -> #f:cmp a -> Tot (ordset a f)

val tail (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) : ordset a f
val head (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) : a 

val mem          : #a:eqtype -> #f:cmp a -> a -> s:ordset a f -> Tot bool

(* currying-friendly version of mem, ready to be used as a lambda *)
unfold let mem_of #a #f (s:ordset a f) x = mem x s

val last (#a:eqtype) (#f:cmp a) (s: ordset a f{s <> empty}) 
  : Tot (x:a{(forall (z:a{mem z s}). f z x) /\ mem x s})

(* 
  liat is the reverse of tail, i.e. a list of all but the last element.
  A shortcut to (fst (unsnoc s)), which as a word is composed
  in a remarkably similar fashion.
*)
val liat (#a:eqtype) (#f:cmp a) (s: ordset a f{s <> empty}) : Tot (l:ordset a f{
    (forall x. mem x l = (mem x s && (x <> last s))) /\
    (if tail s <> empty then (l <> empty) && (head s = head l) else true)
  })

val unsnoc (#a:eqtype) (#f:cmp a) (s: ordset a f{s <> empty}) : Tot (p:(ordset a f & a){
    p = (liat s, last s) 
  }) 

val as_list (#a:eqtype) (#f:cmp a) (s:ordset a f) : Tot (l:list a{
  sorted f l /\
  (forall x. (List.Tot.mem x l = mem x s))   
})

val distinct (#a:eqtype) (f:cmp a) (l: list a) : Pure (ordset a f) 
  (requires True) (ensures fun z -> forall x. (mem x z = List.Tot.Base.mem x l))

val union        : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
val intersect    : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

val choose       : #a:eqtype -> #f:cmp a -> s:ordset a f -> Tot (option a)
val remove       : #a:eqtype -> #f:cmp a -> a -> ordset a f -> Tot (ordset a f)

val size         : #a:eqtype -> #f:cmp a -> ordset a f -> Tot nat

val subset       : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
let superset #a #f (s1 s2: ordset a f) : Tot bool = subset s2 s1

val singleton    : #a:eqtype -> #f:cmp a -> a -> Tot (ordset a f)

val minus        : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

val strict_subset: #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
let strict_superset #a #f (s1 s2: ordset a f) : Tot bool = strict_subset s2 s1

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
 
val mem_union: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
               -> Lemma (requires True)
                        (ensures (mem #a #f x (union #a #f s1 s2) =
                                  (mem #a #f x s1 || mem #a #f x s2)))
                  [SMTPat (mem #a #f x (union #a #f s1 s2))]

val mem_intersect: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
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
    (requires (forall x y. (x `fa` y ==> g x `fb` g y) /\ (x = y <==> g x = g y)))
    (ensures (fun sb -> (size sb <= size sa) /\  
                     (as_list sb == FStar.List.Tot.map g (as_list sa)) /\
                     (let sa = as_list sa in
                      let sb = as_list sb in
                      Cons? sb ==> Cons? sa /\ Cons?.hd sb == g (Cons?.hd sa))))

val lemma_strict_subset_size (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires (strict_subset s1 s2))
          (ensures  (subset s1 s2 /\ size s1 < size s2))
    [SMTPat (strict_subset s1 s2)]

val lemma_minus_mem (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (x:a)
  : Lemma (requires True) (ensures (mem x (minus s1 s2) = (mem x s1 && not (mem x s2))))
    [SMTPat (mem x (minus s1 s2))]

val lemma_strict_subset_exists_diff (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) 
  : Lemma (requires subset s1 s2)
          (ensures (strict_subset s1 s2) <==> (exists x. (mem x s2 /\ not (mem x s1)))) 

type condition a = a -> bool

let inv #a (c: condition a) : (z:condition a{forall x. c x = not (z x)}) = fun x -> not (c x)

val count (#a:eqtype) (#f: cmp a) (s: ordset a f) (c: condition a) : nat

val count_of_empty (#a:eqtype) (#f: cmp a) (s: ordset a f{size s = 0}) (c: condition a)
  : Lemma (count s c = 0)

val count_of_impossible (#a:eqtype) (#f: cmp a) (s: ordset a f) (c: condition a{forall p. not (c p)})
  : Lemma (count s c = 0)

val count_all (#a:eqtype) (#f: cmp a) (s: ordset a f) (c: condition a{forall p. c p})
  : Lemma (count s c = size s)

val count_of_cons (#a:eqtype) (#f: cmp a) (s: ordset a f{size s > 0}) (c: condition a)
  : Lemma (count s c = (count (tail s) c + (if (c (head s)) then 1 else 0)))

val all (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : Tot bool

val any (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : Tot bool

val mem_if_any (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) (x:a{mem x s && c x})
  : Lemma (any s c) 
  
val all_means_not_any_not (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) 
  : Lemma (all s c = not (any s (inv c))) 

val find_first (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : option a  

val find_first_is_some_iff_any (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) 
  : Lemma (Some? (find_first s c) = any s c)  

val find_first_precedes_any_other (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) (x:a{mem x s && c x})
  : Lemma (Some? (find_first s c) && f (Some?.v (find_first s c)) x) 

val liat_size (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty})
  : Lemma (size (liat s) = ((size s)-1))

val mem_liat (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) (x:a)
  : Lemma (mem x s = (mem x (liat s) || x = last s))

val any_liat (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) (c:condition a)
  : Lemma (any s c = (any (liat s) c || c (last s)))

val find_last (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : (z:option a{ match z with
  | None -> not (any s c)
  | Some v -> (any s c /\ (forall (x:a{mem x s && c x}). f x v))
})

val find_last_is_some_iff_any (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) 
  : Lemma (Some? (find_last s c) = any s c)  

val find_last_follows_any_other (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) (x:a{mem x s && c x})
  : Lemma (Some? (find_last s c) && f x (Some?.v (find_last s c))) 

val size_of_tail (#a:eqtype) (#f:cmp a) (s:ordset a f{size s > 0})
  : Lemma (size s = 1 + (size (tail s)))

val count_of_tail (#a:eqtype) (#f:cmp a) (s:ordset a f{size s > 0}) (c: condition a)
  : Lemma (count s c = (count (tail s) c + (if c (head s) then 1 else 0))) 

val where (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) 
  : Pure (ordset a f) 
         (requires True)
         (ensures fun (z:ordset a f) -> 
               (as_list #a  z == FStar.List.Tot.Base.filter c (as_list s)) /\
               (forall x. mem x z = (mem x s && c x)) /\
               (if size z > 0 && size s > 0 then f (head s) (head z) else true))

val intersect_eq_where (#a:eqtype) (#f:cmp a) (s1 s2:ordset a f)  
  : Lemma (intersect s1 s2 = where s1 (mem_of s2))

val minus_eq_where (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (minus s1 s2 = where s1 (inv (mem_of s2))) 
 
val count_is_size_of_where (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a)
  : Lemma (count s c = size (where s c)) 

val size_of_intersect (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f) 
  : Lemma (ensures size (intersect s1 s2) = count s1 (mem_of s2) /\
                   size (intersect s1 s2) = count s2 (mem_of s1))

val size_of_union (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (size (union s1 s2) = (size s1 + size s2 - size (intersect s1 s2)))

val count_dichotomy (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a)
  : Lemma (size s = count s c + count s (inv c))  

val size_of_minus (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (size (minus s1 s2) = size s1 - size (intersect s1 s2))

val intersect_with_subset (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2) 
          (ensures intersect s1 s2 = s1)
  
val lemma_strict_subset_minus_size (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s:ordset a f)
  : Lemma (requires (strict_subset s1 s2 /\ subset s1 s /\ subset s2 s))
          (ensures  (size (minus s s2) < size (minus s s1)))
    [SMTPat (strict_subset s1 s2); SMTPat (subset s1 s); SMTPat (subset s2 s)]

val lemma_disjoint_union_subset (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires (~ (s1 == empty) /\ ~ (s2 == empty) /\ intersect s1 s2 == empty))
          (ensures  (strict_subset s1 (union s1 s2) /\ strict_subset s2 (union s1 s2)))
    [SMTPatOr [[SMTPat (strict_subset s1 (union s1 s2))]; [SMTPat (strict_subset s2 (union s1 s2))]]]

val lemma_subset_union (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s:ordset a f)
  : Lemma (requires (subset s1 s /\ subset s2 s))
          (ensures  (subset (union s1 s2) s))
    [SMTPat (subset (union s1 s2) s)]

val lemma_strict_subset_transitive (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  : Lemma (requires (strict_subset s1 s2 /\ strict_subset s2 s3))
          (ensures  (strict_subset s1 s3))
    [SMTPat (strict_subset s1 s2); SMTPat (strict_subset s2 s3)]

val lemma_intersect_symmetric (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires True) (ensures (intersect s1 s2 == intersect s2 s1))
    [SMTPatOr [[SMTPat (intersect s1 s2)]; [SMTPat (intersect s2 s1)]]]

val lemma_intersect_union_empty (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  : Lemma ((intersect (union s1 s2) s3 = empty) = (intersect s1 s3 = empty && intersect s2 s3 = empty))
    [SMTPat (intersect (union s1 s2) s3)]
 
val lemma_union_symmetric (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (union s1 s2 == union s2 s1)
    [SMTPat (union s1 s2)]

val union_of_disjoint (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires (disjoint s1 s2))
        (ensures (minus (union s1 s2) s1 == s2))
    [SMTPat (union s1 s2); SMTPat (disjoint s1 s2)]

val distinct_is_idempotent (#a:eqtype) (#f: cmp a) (s: ordset a f)
  : Lemma (distinct f (as_list s) = s)

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
