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
module Seq
#set-options "--no_fs_typ_app"
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 "

type seq : Type -> Type

(* Destructors *)
val length: a:Type -> seq a -> Tot nat
val index:  a:Type -> s:seq a -> i:nat{i < length s} -> Tot a

(* Constructors *)
val create: a:Type -> nat -> a -> Tot (seq a)
val upd:    a:Type -> s:seq a -> n:nat{n < length s} -> a ->  Tot (seq a)
val append: a:Type -> seq a -> seq a -> Tot (seq a)
val slice:  a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (seq a)

(* Lemmas about length *)
val lemma_create_len: a:Type -> n:nat -> i:a -> Lemma
  (requires True)
  (ensures (length (create n i) = n))
  [SMTPat (length (create n i))]

val lemma_len_upd: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (length (upd s n v) = length s))
  [SMTPat (length (upd s n v))]

val lemma_len_append: a:Type -> s1:seq a -> s2:seq a -> Lemma
  (requires True)
  (ensures (length (append s1 s2) = length s1 + length s2))
  [SMTPat (length (append s1 s2))]

val lemma_len_slice: a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
  (requires True)
  (ensures (length (slice s i j) = j - i))
  [SMTPat (length (slice s i j))]

(* Lemmas about index *)
val lemma_index_create: a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
  (requires True)
  (ensures (index (create n v) i = v))
  [SMTPat (index (create n v) i)]

val lemma_index_upd1: a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> Lemma
  (requires True)
  (ensures (index (upd s n v) n = v))
  [SMTPat (index (upd s n v) n)]

val lemma_index_upd2: a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> i:nat{i<>n /\ i < length s} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i = index s i))
  [SMTPat (index (upd s n v) i)]

val lemma_index_app1: a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i = index s1 i))
  [SMTPat (index (append s1 s2) i)]

val lemma_index_app2: a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1 + length s2 /\ length s1 <= i} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i = index s2 (i - length s1)))
  [SMTPat (index (append s1 s2) i)]

val lemma_index_slice: a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> k:nat{k < j - i} -> Lemma
  (requires True)
  (ensures (index (slice s i j) k = index s (k + i)))
  [SMTPat (index (slice s i j) k)]

(* Extensionality *)
type Eq: #a:Type -> seq a -> seq a -> Type
val lemma_eq_intro: a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (length s1 = length s2 
               /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i))))
     (ensures (Eq s1 s2))
     [SMTPatT (Eq s1 s2)]

val lemma_eq_refl: a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (s1 = s2))
     (ensures (Eq s1 s2))
     [SMTPatT (Eq s1 s2)]

val lemma_eq_elim: a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (Eq s1 s2))
     (ensures (s1=s2))
     [SMTPatT (Eq s1 s2)]
