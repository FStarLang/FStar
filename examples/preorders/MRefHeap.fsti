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
module MRefHeap

open FStar.Preorder

(* Heap is a tuple of a source of freshness (the no. of the next fresh
   reference to be allocated) and a mapping of allocated raw references
   (represented as natural numbers) to types, values and preorders. *)

let preorder_t (a:Type0) = preorder a

val heap : Type u#1

(* References. *)

val mref (a:Type) (r:preorder_t a) : Type0

val addr_of (#a:Type) (#r:preorder_t a) (m:mref a r) : nat


(* Containment predicate on heaps. *)

val contains (#a:Type) (#r:preorder_t a) (h:heap) (m:mref a r) : Type0

val contains_same_addr_lemma (#a:Type) (#b:Type) (#r:preorder_t a) (#s:preorder_t b) (h:heap) (m:mref a r) (m':mref b s)
  : Lemma (contains h m /\ contains h m' /\ addr_of m = addr_of m' ==> a == b /\ r == s)
    [SMTPat (contains h m); SMTPat (contains h m'); SMTPat (addr_of m); SMTPat (addr_of m')]

val contains_diff_addr_lemma (#a:Type) (#b:Type) (#r:preorder_t a) (#s:preorder_t b) (h:heap) (m:mref a r) (m':mref b s)
  : Lemma (contains h m /\ contains h m' /\ ~(addr_of m = addr_of m') ==> ~(m === m'))
    [SMTPat (contains h m); SMTPat (contains h m'); SMTPat (addr_of m); SMTPat (addr_of m')]

(* Select. *)

val sel : #a:Type ->
          #r:preorder a ->
          h:heap ->
	  m:mref a r{contains h m} ->
          a


(* Generating a fresh reference for the given heap. *)

val alloc_ref : h0:heap ->
		a:Type ->
		r:preorder a ->
	        x:a ->
		Tot (mh1:(mref a r * heap){~(contains #a #r h0 (fst mh1)) /\
		                           contains (snd mh1) (fst mh1) /\
		                           sel (snd mh1) (fst mh1) == x /\
					   (forall b r' (m:mref b r') .
			                      contains h0 m
			                      ==>
			                      contains (snd mh1) m) /\
			                   (forall b r' (m:mref b r'{contains h0 m}) y .
			                      sel #b h0 m == y
		                              ==>
			                      sel #b (snd mh1) m == y)})


(* Update. *)

val upd : #a:Type ->
	  #r:preorder a ->
          h0:heap ->
          m:mref a r{contains h0 m} ->
          x:a ->
          Tot (h1:heap{contains h1 m /\
	               sel h1 m == x /\
		       (forall b r' (m':mref b r') .
			  contains h0 m'
			  ==>
			  contains h1 m') /\
		       (forall b r' (m':mref b r'{contains h0 m'}).{:pattern (sel h0 m') \/ (sel h1 m')}
		          ((addr_of m' <> addr_of m) \/
                           ~(m === m')) ==>
			  sel h0 m' == sel h1 m')})

(* Empty. *)

val emp : heap
