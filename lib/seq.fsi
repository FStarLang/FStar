module Seq

type seq : Type -> Type

(* Destructors *)
assume val length: a:Type -> seq a -> Tot nat
assume val index:  a:Type -> s:seq a -> i:nat{i < length s} -> Tot a

(* Constructors *)
assume val create: a:Type -> nat -> a -> Tot (seq a)
assume val upd:    a:Type -> n:nat -> a -> s:seq a{n < length s} -> Tot (seq a)
assume val append: a:Type -> seq a -> seq a -> Tot (seq a)
assume val slice:  a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (seq a)

(* The following lemmas, introduced to the SMT solver, 
   allow reasoning about the primitives equationally. *)

(* Lemmas about length *)
assume val lemma_create_len: a:Type -> n:nat -> i:a -> Lemma
  (requires True)
  (ensures (length (create n i) = n))
  [SMTPat (length (create n i))]

assume val lemma_len_upd: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (length (upd n v s) = length s))
  [SMTPat (length (upd n v s))]

assume val lemma_len_append: a:Type -> s1:seq a -> s2:seq a -> Lemma
  (requires True)
  (ensures (length (append s1 s2) = length s1 + length s2))
  [SMTPat (length (append s1 s2))]

assume val lemma_len_slice: a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
  (requires True)
  (ensures (length (slice s i j) = j - i))
  [SMTPat (length (slice s i j))]

(* Lemmas about index *)
assume val lemma_index_create: a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
  (requires True)
  (ensures (index (create n v) i = v))
  [SMTPat (index (create n v) i)]

assume val lemma_index_upd1: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (index (upd n v s) n = v))
  [SMTPat (index (upd n v s) n)]

assume val lemma_index_upd2: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> i:nat{i<>n /\ i < length s} -> Lemma
  (requires True)
  (ensures (index (upd n v s) i = index s i))
  [SMTPat (index (upd n v s) i)]

assume val lemma_index_app1: a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i = index s1 i))
  [SMTPat (index (append s1 s2) i)]

assume val lemma_index_app2: a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1 + length s2 /\ length s1 <= i} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i = index s2 (i - length s1)))
  [SMTPat (index (append s1 s2) i)]

assume val lemma_index_slice: a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> k:nat{k < j - i} -> Lemma
  (requires True)
  (ensures (index (slice s i j) k = index s (k + i)))
  [SMTPat (index (slice s i j) k)]

(* Extensionality *)
assume type Eq: #a:Type -> seq a -> seq a -> Type
assume Equals:  forall (a:Type) (s1:seq a) (s2:seq a).{:pattern (Eq s1 s2)}             
  Eq s1 s2 <==> 
  (length s1 = length s2 /\
  (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i)))
assume Extensional: forall (a:Type) (s1:seq a) (s2:seq a).{:pattern (Eq s1 s2)}             
  Eq s1 s2 <==> s1==s2
