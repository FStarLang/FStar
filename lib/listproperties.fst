(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module ListProperties
open List


(** Properties about mem **)

val mem_empty : x:'a ->
  Lemma (requires (mem x []))
        (ensures False)
let mem_empty x = ()


(** Properties about rev **)

val rev_acc_length : l:list 'a -> acc:list 'a ->
  Lemma (requires True)
        (ensures (length (rev_acc l acc) = length l + length acc))
let rec rev_acc_length l acc = match l with
    | [] -> ()
    | hd::tl -> rev_acc_length tl (hd::acc)

val rev_length : l:list 'a ->
  Lemma (requires True)
        (ensures (length (rev l) = length l))
let rev_length l = rev_acc_length l []

val rev_acc_mem : l:list 'a -> acc:list 'a -> x:'a ->
  Lemma (requires True)
        (ensures (mem x (rev_acc l acc) <==> (mem x l \/ mem x acc)))
let rec rev_acc_mem l acc x = match l with
    | [] -> ()
    | hd::tl -> rev_acc_mem tl (hd::acc) x

val rev_mem : l:list 'a -> x:'a ->
  Lemma (requires True)
        (ensures (mem x (rev l) <==> mem x l))
let rev_mem l x = rev_acc_mem l [] x


(** Properties about append **)

val append_nil_l: l:list 'a ->
  Lemma (requires True)
        (ensures ([]@l = l))
let append_nil_l l = ()

val append_l_nil: l:list 'a ->
  Lemma (requires True)
        (ensures (l@[] = l))
let rec append_l_nil = function
  | [] -> ()
  | hd::tl -> append_l_nil tl

val append_cons_l: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures (((hd::tl)@l) = (hd::(tl@l))))
let append_cons_l hd tl l = ()

val append_l_cons: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures ((l@(hd::tl)) = ((l@[hd])@tl)))
let rec append_l_cons hd tl l = match l with
    | [] -> ()
    | hd'::tl' -> append_l_cons hd tl tl'

val append_assoc: l1:list 'a -> l2:list 'a -> l3:list 'a ->
  Lemma (requires True)
        (ensures ((l1@(l2@l3)) = ((l1@l2)@l3)))
let rec append_assoc l1 l2 l3 = match l1 with
    | [] -> ()
    | hd::tl -> append_assoc tl l2 l3

val append_length: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures (length (l1@l2) = length l1 + length l2))
let rec append_length l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_length tl l2

val append_mem:  l1:list 'a
              -> l2:list 'a
              -> a:'a
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
let rec append_mem l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

val append_count:  l1:list 'a
              -> l2:list 'a
              -> a:'a
              -> Lemma (requires True)
                       (ensures (count a (l1@l2) = (count a l1 + count a l2)))
let rec append_count l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_count tl l2 a

val append_eq_nil: l1:list 'a -> l2:list 'a ->
  Lemma (requires (l1@l2 = []))
        (ensures (l1 = [] /\ l2 = []))
let append_eq_nil l1 l2 = ()

val append_eq_singl: l1:list 'a -> l2:list 'a -> x:'a ->
  Lemma (requires (l1@l2 = [x]))
        (ensures ((l1 = [x] /\ l2 = []) \/ (l1 = [] /\ l2 = [x])))
let append_eq_singl l1 l2 x = ()

val append_inv_head: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l@l1) = (l@l2)))
        (ensures (l1 = l2))
let rec append_inv_head l l1 l2 = match l with
    | [] -> ()
    | hd::tl -> append_inv_head tl l1 l2

val append_inv_tail: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l1@l) = (l2@l)))
        (ensures (l1 = l2))
let rec append_inv_tail l l1 l2 = match l1, l2 with
    | [], [] -> ()
    | hd1::tl1, hd2::tl2 -> append_inv_tail l tl1 tl2
    | [], hd2::tl2 ->
       (match l with
          | [] -> ()
          | hd::tl -> append_l_cons hd tl tl2; append_inv_tail tl [] (tl2@[hd])
       (* We can here apply the induction hypothesis thanks to termination on a lexicographical ordering of the arguments! *)
       )
    | hd1::tl1, [] ->
       (match l with
          | [] -> ()
          | hd::tl -> append_l_cons hd tl tl1; append_inv_tail tl (tl1@[hd]) []
       (* Idem *)
       )


(** Properties mixing rev and append **)

val rev': list 'a -> Tot (list 'a)
let rec rev' = function
  | [] -> []
  | hd::tl -> (rev' tl)@[hd]
let rev'T = rev'

val rev_acc_rev': l:list 'a -> acc:list 'a ->
  Lemma (requires (True))
        (ensures ((rev_acc l acc) = ((rev' l)@acc)))
let rec rev_acc_rev' l acc = match l with
    | [] -> ()
    | hd::tl -> rev_acc_rev' tl (hd::acc); append_l_cons hd acc (rev' tl)

val rev_rev': l:list 'a ->
  Lemma (requires True)
        (ensures ((rev l) = (rev' l)))
let rev_rev' l = rev_acc_rev' l []; append_l_nil (rev' l)

val rev'_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev' (l1@l2)) = ((rev' l2)@(rev' l1))))
let rec rev'_append l1 l2 = match l1 with
    | [] -> append_l_nil (rev' l2)
    | hd::tl -> rev'_append tl l2; append_assoc (rev' l2) (rev' tl) [hd]

val rev_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev (l1@l2)) = ((rev l2)@(rev l1))))
let rev_append l1 l2 = rev_rev' l1; rev_rev' l2; rev_rev' (l1@l2); rev'_append l1 l2

val rev'_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev' (rev' l) = l))
let rec rev'_involutive = function
  | [] -> ()
  | hd::tl -> rev'_append (rev' tl) [hd]; rev'_involutive tl

val rev_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev (rev l) = l))
let rev_involutive l = rev_rev' l; rev_rev' (rev' l); rev'_involutive l


(** Reverse induction principle **)

val rev'_list_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p (rev' tl) ==> p (rev' (hd::tl)))))
        (ensures (p (rev' l)))
let rec rev'_list_ind p = function
  | [] -> ()
  | hd::tl -> rev'_list_ind p tl

val rev_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p hd ==> p (hd@[tl]))))
        (ensures (p l))
let rev_ind p l = rev'_involutive l; rev'_list_ind p (rev' l)


(** Properties about partition **)

val partition_length: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures (length (fst (partitionT f l)) + length (snd (partitionT f l)) = length l))
let partition_length f l = List.partition_length f l

val partition_mem: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures ((fun l1 l2 ->
                                     (forall x. mem x l1 ==> f x)
                                      /\ (forall x. mem x l2 ==> not (f x))
                                      /\ (forall x. mem x l = (mem x l1 || mem x l2))))
                                        (fst (partitionT f l))
                                        (snd (partitionT f l)))
let rec partition_mem f l = match l with
  | [] -> ()
  | hd::tl -> partition_mem f tl

val partition_count: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures (forall x. count x l = (count x (fst (partitionT f l)) + count x (snd (partitionT f l)))))
let rec partition_count f l = match l with
  | [] -> ()
  | hd::tl -> partition_count f tl


(** Correctness of quicksort **)

val sorted: ('a -> 'a -> Tot int) -> list 'a -> Tot bool
let rec sorted f = function
  | []
  | [_] -> true
  | x::y::tl -> f x y > 0 && sorted f (y::tl)

opaque type total_order (a:Type) (f: (a -> a -> Tot int)) =
    (forall a. f a a = 0)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 > 0) <==> (f a2 a1 < 0))   (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 >= 0 /\ f a2 a3 >= 0 ==> f a1 a3 >= 0)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 = 0 ==> a1 <> a2) (* Totality *)

val append_sorted:  a:Type
               ->  f:(a -> a -> Tot int)
               ->  l1:list a{sorted f l1}
               ->  l2:list a{sorted f l2}
               ->  pivot:a
               ->  Lemma (requires (total_order a f)
                                    /\ (forall y. mem y l1 ==> f pivot y <= 0)
                                    /\ (forall y. mem y l2 ==> f pivot y > 0))
                         (ensures (sorted f (l1@(pivot::l2))))
let rec append_sorted f l1 l2 pivot = match l1 with
  | [] -> ()
  | hd::tl -> append_sorted f tl l2 pivot

val sortWithT_sorted: f:('a -> 'a -> Tot int) ->  l:list 'a ->
  Lemma (requires (total_order 'a f))
        (ensures (sorted f (sortWithT f l) /\ (forall x. count x l = count x (sortWithT f l))))
        (decreases (length l))
let rec sortWithT_sorted f = function
  | [] -> ()
  | pivot::tl ->
     let hi, lo  = partitionT (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     (* How can it work with these two lines commented out? *)
     (* partition_mem (bool_of_compare f pivot) tl; *)
     (* partition_count (bool_of_compare f pivot) tl; *)
     sortWithT_sorted f lo;
     sortWithT_sorted f hi;
     append_sorted _ f (sortWithT f lo) (sortWithT f hi) pivot
