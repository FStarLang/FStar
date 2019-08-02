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
module ArrayUtils

open FStar.Seq

(*
 * some utilities for the array library, mostly straightforward manipulations of sequences
 *)

(*****)

let init_at_seq (#a:Type0) (s:seq (option a)) (i:nat{i < length s}) :Type0
  = Some? (index s i)

let all_some (#a:Type0) (s:seq (option a)) :Type0
  = forall (i:nat). i < length s ==> Some? (index s i)

(*
 * a sequence of option a is equivalent to a sequence of a, if all are Some and contained values match
 *)
let some_equivalent_seqs (#a:Type0) (s1:Seq.seq (option a)) (s2:Seq.seq a) :Type0
  = (Seq.length s1 == Seq.length s2) /\
    (forall (i:nat). i < Seq.length s1 ==> Some (Seq.index s2 i) == Seq.index s1 i)

(*
 * given a sequence of option a, where all indices have Some values, get a seq a
 *)
assume val get_some_equivalent (#a:Type0) (s:Seq.seq (option a))
  : Pure (seq a)
         (requires (all_some s))
	 (ensures  (fun r -> some_equivalent_seqs s r))

let lemma_get_some_equivalent_length (#a:Type0) (s:seq (option a))
  :Lemma (requires (all_some s))
         (ensures  (all_some s /\
	            length (get_some_equivalent s) == length s))
	 [SMTPat (length (get_some_equivalent s))]
  = ()

let lemma_get_some_equivalent_index (#a:Type0) (s:seq (option a)) (i:nat)
  :Lemma (requires (all_some s /\ i < length s))
         (ensures  (all_some s /\ i < length s /\
	            Some? (index s i) /\ Some (index (get_some_equivalent s) i) == index s i))
	 [SMTPat (index (get_some_equivalent s) i)]
  = ()

assume val lemma_get_some_equivalent_snoc (#a:Type0) (s:seq (option a)) (x:option a)
  :Lemma (requires (all_some s /\ Some? x))
         (ensures  (all_some s /\ Some? x /\
	            get_some_equivalent (snoc s x) == snoc (get_some_equivalent s) (Some?.v x)))
	 [SMTPatOr [[SMTPat (get_some_equivalent (snoc s x))]; [SMTPat (snoc (get_some_equivalent s) (Some?.v x))]]]

assume val lemma_get_some_equivalent_append (#a:Type0) (s1:seq (option a)) (s2:seq (option a))
  :Lemma (requires (all_some s1 /\ all_some s2))
         (ensures  (all_some s1 /\ all_some s2 /\
	            get_some_equivalent (append s1 s2) == append (get_some_equivalent s1) (get_some_equivalent s2)))
	 [SMTPatOr [[SMTPat (get_some_equivalent (append s1 s2))]; [SMTPat (append (get_some_equivalent s1) (get_some_equivalent s2))]]]

assume val lemma_get_some_equivalent_slice (#a:Type0) (s:seq (option a)) (i:nat) (j:nat)
  :Lemma (requires (all_some s /\ j >= i /\ j <= Seq.length s))
         (ensures  (all_some s /\ j >= i /\ j <= Seq.length s /\
	            get_some_equivalent (slice s i j) == slice (get_some_equivalent s) i j))

	 [SMTPatOr [[SMTPat (get_some_equivalent (slice s i j))]; [SMTPat (slice (get_some_equivalent s) i j)]]]

let lemma_get_equivalent_sequence_slice
  (#a:Type0) (s:seq (option a)) (i:nat) (j:nat)
  (s':seq a)
  :Lemma (requires (j >= i /\ j <= Seq.length s /\
                    Seq.length s' = j - i    /\
		    (forall (k:nat). (k >= i /\ k < j) ==> Seq.index s k == Some (Seq.index s' (k - i)))))
         (ensures  (j >= i /\ j <= Seq.length s /\
                    Seq.length s' = j - i    /\
		    (forall (k:nat). (k >= i /\ k < j) ==> Seq.index s k == Some (Seq.index s' (k - i))) /\
	            get_some_equivalent (Seq.slice s i j) == s'))
  = admit ()

assume val copy_seq (#a:Type0) (s1:seq (option a)) (i:nat) (j:nat) (s2:seq a)
  :Pure (seq (option a))
        (requires (j >= i /\ j <= Seq.length s1 /\ Seq.length s2 = j - i))
	(ensures  (fun r -> j >= i /\ j <= Seq.length s1 /\ Seq.length s2 = j - i /\
	                 Seq.length r == Seq.length s1                      /\
			 (forall (off:nat) (n:nat). (off + n <= Seq.length s1 /\ (off + n <= i \/ j <= off)) ==>
			                    Seq.slice s1 off (off + n) == Seq.slice r off (off + n))  /\
                         (forall (k:nat).
			    (k < i ==> (Seq.index r k == Seq.index s1 k)) /\
			    ((k >= i /\ k < j) ==> (Seq.index r k == Some (Seq.index s2 (k - i)))) /\
		            ((k >= j /\ k < Seq.length s1) ==> (Seq.index r k == Seq.index s1 k))))) 

let is_prefix_of (#a:Type) (s1:seq a) (s2:seq a) :Type0
  = length s1 <= length s2 /\
    (forall (i:nat). i < length s1 ==> Seq.index s1 i == Seq.index s2 i)

let lemma_is_prefix_of_slice
  (#a:Type0) (s1:seq a) (s2:seq a{s1 `is_prefix_of` s2}) (i:nat) (j:nat{j >= i /\ j <= Seq.length s1})
  :Lemma (requires True)
         (ensures  (Seq.slice s1 i j == Seq.slice s2 i j))
	 [SMTPat (s1 `is_prefix_of` s2); SMTPat (Seq.slice s1 i j); SMTPat (Seq.slice s2 i j)]
  = admit ()

assume val seq_map:
  #a:Type -> #b:Type -> f:(a -> b) -> s:seq a
  -> (r:seq b{length s = length r /\ (forall (i:nat). i < length s ==> Seq.index r i == f (Seq.index s i))})

assume val lemma_map_commutes_with_prefix:
  #a:Type -> #b:Type -> f:(a -> b) -> s1:seq a -> s2:seq a
  -> Lemma (requires (s1 `is_prefix_of` s2))
          (ensures  (seq_map f s1 `is_prefix_of` seq_map f s2))
 
assume val lemma_map_commutes_with_snoc:
  #a:Type -> #b:Type -> f:(a -> b) -> s:seq a -> x:a
  -> Lemma (seq_map f (snoc s x) == snoc (seq_map f s) (f x))
