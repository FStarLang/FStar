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

(* A logical theory of sequences indexed by natural numbers in [0, n) *)
module FStar.Seq.Base
//#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

module List = FStar.List.Tot

new val seq ([@@@strictly_positive] a : Type u#a) : Type u#a

(* Destructors *)
val length: #a:Type -> seq a -> Tot nat

val seq_to_list (#a:Type) (s:seq a) : Tot (l:list a{List.length l == length s})

val seq_of_list (#a:Type) (l:list a) : Tot (s:seq a{List.length l == length s})

val index:  #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a

val create: #a:Type -> nat -> a -> Tot (seq a)

private val init_aux (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> Tot a))
  :Tot (seq a)

inline_for_extraction val init: #a:Type -> len:nat -> contents: (i:nat { i < len } -> Tot a) -> Tot (seq a)

private val init_aux_ghost (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> GTot a))
  : GTot (seq a)

inline_for_extraction val init_ghost: #a:Type -> len:nat -> contents: (i:nat { i < len } -> GTot a) -> GTot (seq a)

val empty (#a:Type) : Tot (s:(seq a){length s=0})

[@@(deprecated "Seq.empty")]
unfold
let createEmpty (#a:Type)
    : Tot (s:(seq a){length s=0})
    = empty #a

val lemma_empty (#a:Type) (s:seq a) : Lemma (length s = 0 ==> s == empty #a)

val upd: #a:Type -> s:seq a -> n:nat{n < length s} -> a ->  Tot (seq a)

val append: #a:Type -> seq a -> seq a -> Tot (seq a)

let cons (#a:Type) (x:a) (s:seq a) : Tot (seq a) = append (create 1 x) s

let op_At_Bar (#a:Type) (s1:seq a) (s2:seq a) = append s1 s2

val slice:  #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (seq a)

(* Lemmas about seq_to_list/seq_of_list *)
val lemma_seq_of_seq_to_list : #a:Type -> s:seq a ->
  Lemma
  (requires True)
  (ensures seq_of_list (seq_to_list s) == s)
  [SMTPat (seq_of_list (seq_to_list s))]

val lemma_seq_to_seq_of_list : #a:Type -> l:list a ->
  Lemma
  (requires True)
  (ensures seq_to_list (seq_of_list l) == l)
  [SMTPat (seq_to_list (seq_of_list l))]

val lemma_seq_of_list_cons : #a:Type -> x:a -> l:list a ->
  Lemma
  (requires True)
  (ensures seq_of_list (x::l) == create 1 x @| seq_of_list l)
  [SMTPat (seq_of_list (x::l))]

val lemma_seq_to_list_cons : #a:Type -> x:a -> s:seq a ->
  Lemma
  (requires True)
  (ensures seq_to_list (cons x s) == x :: seq_to_list s)
  [SMTPat (seq_to_list (cons x s))]

(* Lemmas about length *)
val lemma_create_len: #a:Type -> n:nat -> i:a -> Lemma
  (requires True)
  (ensures (length (create n i) = n))
  [SMTPat (length (create n i))]

val lemma_init_len: #a:Type -> n:nat -> contents: (i:nat { i < n } -> Tot a) -> Lemma
  (requires True)
  (ensures (length (init n contents) = n))
  [SMTPat (length (init n contents))]

private val lemma_init_aux_len (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> Tot a))
  : Lemma (requires True)
    (ensures (length (init_aux n k contents) = n - k))
    [SMTPat (length (init_aux n k contents))]

val lemma_init_ghost_len: #a:Type -> n:nat -> contents: (i:nat { i < n } -> GTot a) -> Lemma
  (requires True)
  (ensures (length (init_ghost n contents) = n))
  [SMTPat (length (init_ghost n contents))]

private val lemma_init_ghost_aux_len (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> GTot a))
  : Lemma (requires True)
    (ensures (length (init_aux_ghost n k contents) = n - k))
    [SMTPat (length (init_aux_ghost n k contents))]

val lemma_len_upd: #a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (length (upd s n v) = length s))
  [SMTPat (length (upd s n v))]

val lemma_len_append: #a:Type -> s1:seq a -> s2:seq a -> Lemma
  (requires True)
  (ensures (length (append s1 s2) = length s1 + length s2))
  [SMTPat (length (append s1 s2))]

val lemma_len_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
  (requires True)
  (ensures (length (slice s i j) = j - i))
  [SMTPat (length (slice s i j))]

(* Lemmas about index *)
val lemma_index_create: #a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
  (requires True)
  (ensures (index (create n v) i == v))
  [SMTPat (index (create n v) i)]

val lemma_index_upd1: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]

val lemma_index_upd2: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> i:nat{i<>n /\ i < length s} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]

val lemma_index_app1: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s1 i))
  [SMTPat (index (append s1 s2) i)]

val lemma_index_app2: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1 + length s2 /\ length s1 <= i} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s2 (i - length s1)))
  [SMTPat (index (append s1 s2) i)]

val lemma_index_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> k:nat{k < j - i} -> Lemma
  (requires True)
  (ensures (index (slice s i j) k == index s (k + i)))
  [SMTPat (index (slice s i j) k)]

val hasEq_lemma: a:Type -> Lemma (requires (hasEq a)) (ensures (hasEq (seq a))) [SMTPat (hasEq  (seq a))]

[@@ remove_unused_type_parameters [0; 1; 2]]
val equal (#a:Type) (s1:seq a) (s2:seq a) : Tot prop

(* decidable equality *)
private val eq_i:
  #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2}
  -> i:nat{i <= length s1}
  -> Tot (r:bool{r <==> (forall j. (j >= i /\ j < length s1) ==> (index s1 j = index s2 j))})

val eq: #a:eqtype -> s1:seq a -> s2:seq a -> Tot (r:bool{r <==> equal s1 s2})

val lemma_eq_intro: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (length s1 = length s2
               /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i))))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]

val lemma_eq_refl: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (s1 == s2))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]

val lemma_eq_elim: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (equal s1 s2))
     (ensures (s1==s2))
     [SMTPat (equal s1 s2)]

(* Properties of [append] *)

val append_assoc
  (#a: Type)
  (s1 s2 s3: seq a)
: Lemma
  (ensures (append (append s1 s2) s3 == append s1 (append s2 s3)))

val append_empty_l
  (#a: Type)
  (s: seq a)
: Lemma
  (ensures (append empty s == s))

val append_empty_r
  (#a: Type)
  (s: seq a)
: Lemma
  (ensures (append s empty == s))


val init_index (#a:Type) (len:nat) (contents:(i:nat { i < len } -> Tot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len}). index (init len contents) i == contents i))

val init_index_ (#a:Type) (len:nat) (contents:(i:nat { i < len } -> Tot a)) (j: nat)
  : Lemma (requires j < len)
    (ensures (index (init len contents) j == contents j))
    [SMTPat (index (init len contents) j)]

val init_ghost_index (#a:Type) (len:nat) (contents:(i:nat { i < len } -> GTot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len}). index (init_ghost len contents) i == contents i))

val init_ghost_index_ (#a:Type) (len:nat) (contents:(i:nat { i < len } -> GTot a)) (j: nat)
  : Lemma (requires j < len)
    (ensures (index (init_ghost len contents) j == contents j))
    [SMTPat (index (init_ghost len contents) j)]

val lemma_equal_instances_implies_equal_types (_:unit)
  :Lemma (forall (a:Type) (b:Type) (s1:seq a) (s2:seq b). s1 === s2 ==> a == b)
