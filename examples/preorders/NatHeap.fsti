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
module NatHeap

open FStar.Preorder

(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

(* NB: (a:Type0 & a) instead of dtuple2 is better notation *)

module F = FStar.FunctionalExtensionality

//abstract
val heap: Type u#1

(* Consistency of heaps. aka, no strong updates *)

val consistent (h0:heap) (h1:heap) : GTot Type0


(* References. *)

val ref (a:Type0) : Type0

//type aref =
//  | Ref : a:Type -> r:ref a -> aref

(* Containment predicate on heaps. *)

val contains (#a:Type) (h:heap) (r:ref a) : GTot Type0
//NB: Some? (snd h r), would avoid the existential, but would not capture the type equality

//NB: match snd h r with | Some (| b, _ |) -> a == b | _ -> False
//    this style would avoid the existential

//NB: Although, it appears that the existential variable actually seems to help in this case
//    would be good to understand why (at some point)

(* Select. *)

val sel : #a:Type -> 
          h:heap ->
	  r:ref a{contains h r} -> 
          Tot a


(* Generating a fresh reference for the given heap. *)

val alloc_ref : h0:heap ->
                a:Type -> 
		x:a -> 
		Tot (rh1:(ref a * heap)
			 {~(contains h0 (fst rh1)) /\ 
			  contains (snd rh1) (fst rh1) /\
		          sel (snd rh1) (fst rh1) == x /\
			  (forall b (r:ref b) .{:pattern (contains h0 r)}
			     contains h0 r 
			     ==> 
			     contains (snd rh1) r) /\
			  (forall b (r:ref b{contains h0 r}) . {:pattern sel #b h0 r}
			     sel #b h0 r == sel #b (snd rh1) r)})


(* Update. *)

val upd : #a:Type -> 
          h0:heap -> 
          r:ref a{contains h0 r} -> 
          x:a -> 
          Tot (h1:heap{contains h1 r /\ 
	               sel h1 r == x /\
		       (forall b (r':ref b) . {:pattern (contains h0 r')}
			  contains h0 r' 
			  ==> 
			  contains h1 r') /\
		       (forall b (r':ref b{contains h0 r'}) . {:pattern sel h0 r'}
		          ~(r === r') ==>
			  sel h0 r' == sel h1 r')})

(* Empty. *)

val emp : heap


(*
(* Domain. *)

open FStar.Set

private val domain_acc : h:heap -> n:nat{n <= fst h} -> Tot (set aref)
let rec domain_acc h n = 
  if n = 0 then empty
           else (match snd h (n - 1) with
	         | Some (| a , _ |) -> let r:ref a = n - 1 in 
		                       union (singleton (Ref a r)) (domain_acc h (n - 1)))  //Universe problem with (Ref a r)


val domain : heap -> Tot (set aref)
let domain h = domain_acc h (fst h)
*)


(* Concatenation. *)
let max (n m:nat) : nat =
  if n > m then n else m
  

val concat : h0:heap -> h1:heap{consistent h0 h1} -> Tot heap

(* Lemmas about the consistency of heaps. *)

val consistent_refl : h:heap ->
                      Lemma (consistent h h)


val emp_consistent : h:heap -> 
                     Lemma (consistent emp h)


val upd_consistent : h:heap ->
                     a:Type ->
		     r:ref a{contains h r} ->
		     x:a ->
                     Lemma (consistent h (upd h r x))

val alloc_ref_consistent : h:heap ->
                           a:Type ->
			   x:a ->
			   Lemma (consistent h (snd (alloc_ref h a x)))


(* Lemmas about (contains). *)

val contains_sel : h:heap -> 
                   a:Type -> 
		   r:ref a{contains h r} -> 
		   Lemma (exists x . sel h r == x)


val contains_upd : h:heap ->                
                   a:Type ->
		   b:Type ->
		   r:ref a{contains h r} ->
		   x:a ->
		   r':ref b ->
		   Lemma (requires (contains h r'))
		         (ensures  (contains (upd h r x) r'))
		   [SMTPat (contains (upd h r x) r')]  


val contains_emp : a:Type -> 
                   r:ref a -> 
		   Lemma (requires (True))
		         (ensures  (~(contains emp r)))
		   [SMTPat (~(contains emp r))]


(* Lemmas about the interaction of (sel) and (upd). *)

val sel_upd1 : h:heap ->
               a:Type -> 
	       r:ref a{contains #a h r} -> 
	       x:a -> 
	       Lemma (requires (True))
	             (ensures  (sel (upd h r x) r == x))
	       [SMTPat (sel (upd h r x) r)]


val sel_upd2 : h:heap ->
               a:Type ->
               b:Type -> 
	       r:ref a{contains #a h r} -> 
	       x:a -> 
	       r':ref b{contains #b h r'} -> 
	       Lemma (requires (~(r === r')))
	             (ensures  (sel (upd h r x) r' == sel h r'))
	       [SMTPat (sel (upd h r x) r')]


val upd_sel : h:heap ->
              a:Type -> 
	      r:ref a{contains #a h r} -> 
	      Lemma (requires (True))
	            (ensures  (upd h r (sel h r) == h))
	      [SMTPat (upd h r (sel h r))]


(* Lemmas about (concat). *)

val contains_concat1 : h0:heap -> 
		       h1:heap{consistent h0 h1} -> 
		       a:Type ->
		       r:ref a -> 
		       Lemma (requires (contains h0 r))
                             (ensures  (contains (concat h0 h1) r))
			     [SMTPat (contains (concat h0 h1) r)]


val contains_concat2 : h0:heap -> 
		       h1:heap{consistent h0 h1} -> 
		       a:Type ->
		       r:ref a -> 
		       Lemma (requires (contains h1 r))
                             (ensures  (contains (concat h0 h1) r))
		       [SMTPat (contains (concat h0 h1) r)]


val sel_concat1 : h0:heap -> 
		  h1:heap{consistent h0 h1} -> 
		  a:Type ->
		  r:ref a{contains h0 r /\ ~(contains h1 r)} -> 
		  Lemma (requires (True))
		        (ensures  (sel (concat h0 h1) r == sel h0 r))
	          [SMTPat (sel (concat h0 h1) r)]

val sel_concat2 : h0:heap -> 
		  h1:heap{consistent h0 h1} -> 
		  a:Type ->
		  r:ref a{contains h1 r} -> 
		  Lemma (requires (True))
		        (ensures  (sel (concat h0 h1) r == sel h1 r))
	          [SMTPat (sel (concat h0 h1) r)]

