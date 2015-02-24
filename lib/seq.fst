(* A logical theory of integer-indexed sequences, from [0, n) *)
module Seq
open FunctionalExtensionality

type seq (a:Type) = { 
  contents: nat -> Tot a;
  length:   nat
}

val create:  a:Type -> nat -> a -> Tot (seq a)
let create len v = {
  contents=(fun i -> v);
  length=len;
}

val index:    a:Type -> s:seq a -> i:nat{i < s.length} -> Tot a
let index s i = s.contents i
                                       
val upd:    a:Type -> n:nat -> a -> s:seq a{n < s.length} -> Tot (seq a)
let upd n v s = {
  contents=(fun i -> if i=n then v else s.contents i);
  length=s.length;
}

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

val length: a:Type -> seq a -> Tot nat
let length s = s.length

val split: a:Type -> s:seq a -> i:nat{(0 <= i /\ i < length s)} -> Tot (seq a * seq a)
let split s i = slice s 0 i, slice s i (length s)

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
let test_index_app1    (a:Type) (s1:seq a) (s2:seq a) (i:nat{i < length s1})                               = assert (index  (append s1 s2) i = index s1 i)
let test_index_app2    (a:Type) (s1:seq a) (s2:seq a) (i:nat{length s1 <= i && i < length s1 + length s2}) = assert (index  (append s1 s2) i = index s2 (i - s1.length))
let test_index_slice   (a:Type) (s:seq a) (i:nat) (j:nat{i <= j && j <= length s}) (k:nat{k < (j - i)})    = assert (index  (slice s i j) k  = index s (i + k))


val lemma_slice_append: a:Type -> s1:seq a{length s1 >= 1} -> s2:seq a -> Lemma (ensures (Eq (append s1 s2) (append (slice s1 0 1) (append (slice s1 1 (length s1)) s2))))
let lemma_slice_append s1 s2 = ()

(* val test_append_inj :   a:Type -> b1:seq a -> b2:seq a -> c1:seq a -> c2:seq a -> Lemma (requires ((length b1 = length c1) *)
(*                                                                                                    /\ Eq (append b1 b2) (append c1 c2))) *)
(*                                                                                         (ensures (Eq b1 c1 /\ Eq b2 c2)) *)
(*                                                                                         (decreases (length b1)) *)
(* let rec test_append_inj b1 b2 c1 c2 = *)
(*   if length b1 = 0 *)
(*   then admit() *)
(*   else (//assert (index (append b1 b2) 0 = index (append c1 c2) 0); *)
(*         assert (index b1 0 = index c1 0); *)
(*         admit ()) *)
(*         (\* assert (append b1 b2 = append (slice b1 0 1) (append (slice b1 1 (length b1)) b2)); *\) *)
(* //        test_append_inj (slice b1 1 (length b1)) b2 (slice c1 1 (length c1)) c2) *)
  

(* let test_append_inj    (a:Type) (b1:seq a) (b2:seq a) (c1:seq a) (c2:seq a) =  *)
(*   assert (length b1 = length c1 /\ Eq (append b1 b2) (append c1 c2) *)
(*           ==> (Eq b1 c1 /\ Eq b2 c2)) *)

(* assume TypeInj:     forall (a:Type) (b:Type) (s1:seq a) (s2:seq b). s1==s2 ==> a==b *)
(* assume AppendInj:   forall (a:Type) (b1:seq a) (b2:seq a) (c1:seq a) (c2:seq a). {:pattern (equal (append b1 b2) (append c1 c2))} *)
(*                                                                          (length b1 == length c1 /\ equal (append b1 b2) (append c1 c2)) *)
(*                                                                          ==> (equal b1 c1 /\ equal b2 c2) *)
(* assume AppendSplit: forall (a:Type) (b:seq a) (i:nat). {:pattern (append (sub b 0 i) (sub b i (length b)))} equal (append (sub b 0 i) (sub b i (length b))) b *)
