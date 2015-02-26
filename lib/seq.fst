(* A logical theory of integer-indexed sequences, from [0, n) *)
module Seq
open FunctionalExtensionality

type seq (a:Type) = { 
  contents: nat -> Tot a;
  length:   nat
}

val length: a:Type -> seq a -> Tot nat
let length s = s.length

val create:  a:Type -> nat -> a -> Tot (seq a)
let create len v = {
  contents=(fun i -> v);
  length=len;
}

val index:    a:Type -> s:seq a -> i:nat{i < s.length} -> Tot a
let index s i = s.contents i

(* val lemma_create_len: a:Type -> n:nat -> i:a -> Lemma *)
(*   (requires True) *)
(*   (ensures (length (create n i) = n)) *)
(*   [SMTPat (length (create n i))]                                                *)
(* let lemma_create_len n i = () *)

(* val lemma_create_index: a:Type -> n:nat -> i:a -> j:nat{j < n} -> Lemma *)
(*   (requires True) *)
(*   (ensures (index (create n i) j = i)) *)
(*   [SMTPat (index (create n i) j)]                                                *)
(* let lemma_create_index n i = () *)

val upd:    a:Type -> n:nat -> a -> s:seq a{n < s.length} -> Tot (seq a)
let upd n v s = {
  contents=(fun i -> if i=n then v else s.contents i);
  length=s.length;
}

(* val lemma_len_upd: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma *)
(*   (requires True) *)
(*   (ensures (length (upd n v s) = n)) *)
(*   [SMTPat (length (upd n v s))] *)
(* let lemma_len_upd n i = () *)

(* val lemma_index_upd1: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma *)
(*   (requires True) *)
(*   (ensures (index (upd n v s) n = n)) *)
(* let lemma_index_upd1 n v s = () *)

(* val lemma_index_upd2: a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> i:nat{i<>n /\ i < length s} -> Lemma *)
(*   (requires True) *)
(*   (ensures (index (upd n v s) i = index s i)) *)
(* let lemma_index_upd2 n v s = () *)

val append: a:Type -> seq a -> seq a -> Tot (seq a)
let append s1 s2 = {
  contents=(fun x -> if x < s1.length then s1.contents x else s2.contents (x - s1.length));
  length=s1.length + s2.length;
}

val slice:    a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= s.length} -> Tot (seq a)
let slice s i j = {
  contents=(fun x -> s.contents (x + i));
  length=j - i;
}

val head: a:Type -> s:seq a{s.length > 0} -> Tot a
let head s = index s 0

val tail: a:Type -> s:seq a{s.length > 0} -> Tot (seq a)
let tail s = {
  contents=(fun (n:nat) -> s.contents (n + 1));
  length=s.length - 1;
}

val cons: a:Type -> a -> seq a -> Tot (seq a)
let cons x s = {
  contents=(fun n -> if n=0 then x else s.contents (n - 1));
  length=s.length + 1;
}


val split: a:Type -> s:seq a -> i:nat{(0 <= i /\ i < length s)} -> Tot (seq a * seq a)
let split s i = slice s 0 i, slice s i (length s)

val count : 'a -> s:seq 'a -> Tot nat (decreases s.length)
let rec count x s = 
  if s.length = 0 then 0
  else if head s = x 
  then 1 + count x (tail s)
  else count x (tail s)

val mem: 'a -> seq 'a -> Tot bool
let mem x l = count x l > 0

val swap: a:Type -> s:seq a -> i:nat{i<s.length} -> j:nat{j<s.length} -> Tot (seq a)
let swap s i j = upd i (index s j) (upd j (index s i) s)

assume type Eq: #a:Type -> seq a -> seq a -> Type
assume Equals:      forall (a:Type) (s1:seq a) (s2:seq a).             {:pattern (Eq s1 s2)}             Eq s1 s2 <==> 
                            (forall (i:nat{i < s1.length && i < s2.length}).{:pattern (index s1 i); (index s2 i)} 
                                                                              (s1.length == s2.length
                                                                               /\ index s1 i == index s2 i))
assume Extensional: forall (a:Type) (s1:seq a) (s2:seq a).             {:pattern (Eq s1 s2)}             Eq s1 s2 <==> s1==s2

val lemma_extensional: a:Type -> s1:seq a -> s2:seq a{Eq s1 s2} -> Lemma (ensures (s1 = s2))
let lemma_extensional s1 s2 = ()

let test_length_create (a:Type) (n:nat) (x:a)                                                              = assert (length (create n x)     = n)
let test_length_upd    (a:Type) (i:nat) (x:a) (s:seq a{i < length s})                                      = assert (length (upd i x s)      = length s)
let test_length_app    (a:Type) (s1:seq a) (s2:seq a)                                                      = assert (length (append s1 s2)   = length s1 + length s2)
let test_length_slice  (a:Type) (s:seq a) (i:nat) (j:nat{i <= j && j <= length s})                         = assert (length (slice s i j)    = j - i)
let test_index_create  (a:Type) (n:nat) (x:a) (i:nat{i<n})                                                 = assert (index  (create n x) i   = x)
let test_index_upd1    (a:Type) (s:seq a) (i:nat{i < length s}) (x:a)                                      = assert (index  (upd i x s) i    = x)
let test_index_upd2    (a:Type) (s:seq a) (i:nat{i < length s}) (j:nat{i<>j && j < s.length}) (x:a)        = assert (index  (upd j x s) i    = index s i)

val lemma_index_slice: a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> k:nat{k < (j - i)} -> Lemma (requires True)
                                                                                                                   (ensures (index  (slice s i j) k  = index s (i + k)))
                                                                                                                   [SMTPat (index  (slice s i j) k)]
let lemma_index_slice   (a:Type) (s:seq a) (i:nat) (j:nat{i <= j && j <= length s}) (k:nat{k < (j - i)})    = ()//assert (index  (slice s i j) k  = index s (i + k))

val lemma_index_app: a:Type -> s1:seq a -> s2:seq a -> i:nat{i < (length s1 + length s2)} 
                     -> Lemma (requires True) 
                              (ensures (   (i < length s1 ==> index (append s1 s2) i = index s1 i))
                                       /\  (length s1 <= i ==> index (append s1 s2) i = index s2 (i - s1.length)))
                              [SMTPat (index (append s1 s2) i)]
let lemma_index_app s1 s2 i = ()

val lemma_slice_append: a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> Lemma (ensures (Eq (append s1 s2) (append (slice s1 0 1) (append (slice s1 1 (length s1)) s2))))
let lemma_slice_append s1 s2 = ()

val lemma_append_cons: a:Type -> s1:seq a{s1.length > 0} -> s2:seq a -> Lemma 
  (requires True)
  (ensures (append s1 s2 = cons (head s1) (append (tail s1) s2)))
let rec lemma_append_cons s1 s2 = 
  cut (Eq (append s1 s2) (cons (head s1) (append (tail s1) s2)))

val lemma_tl: a:Type -> hd:a -> tl:seq a -> Lemma (ensures (tail (cons hd tl) = tl))
let lemma_tl hd tl = cut (Eq (tail (cons hd tl)) tl)

val sorted: ('a -> 'a -> Tot bool) 
          -> s:seq 'a
          -> Tot bool (decreases (s.length))
let rec sorted f s =
  if s.length <= 1
  then true
  else let hd = head s in
       f hd (index s 1) && sorted f (tail s)
