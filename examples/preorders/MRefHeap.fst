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

let heap_cell_a (a:Type0) = a * preorder_t a
let heap_cell = (a:Type0 & heap_cell_a a)
let heap = h:(nat * (nat -> Tot (option heap_cell)))
		       {(forall (n:nat) . n < fst h ==> (exists v . snd h n == Some v)) /\
			(forall (n:nat) . n >= fst h ==> snd h n == None)}

(* References. *)

let mref (a:Type) (r:preorder_t a) = nat

let addr_of (#a:Type) (#r:preorder_t a) (m:mref a r) : nat = m


(* Containment predicate on heaps. *)

let contains (#a:Type) (#r:preorder_t a) (h:heap) (m:mref a r) : GTot Type0 =
  exists (v:heap_cell).
    snd h m == Some v /\
    dfst v == a /\
    snd #(dfst v) #(preorder_t a) (dsnd v) == r

let contains_same_addr_lemma (#a:Type) (#b:Type) (#r:preorder_t a) (#s:preorder_t b) (h:heap) (m:mref a r) (m':mref b s)
  : Lemma (contains h m /\ contains h m' /\ addr_of m = addr_of m' ==> a == b /\ r == s)
    [SMTPat (contains h m); SMTPat (contains h m'); SMTPat (addr_of m); SMTPat (addr_of m')]
  = ()

let contains_diff_addr_lemma (#a:Type) (#b:Type) (#r:preorder_t a) (#s:preorder_t b) (h:heap) (m:mref a r) (m':mref b s)
  : Lemma (contains h m /\ contains h m' /\ ~(addr_of m = addr_of m') ==> ~(m === m'))
    [SMTPat (contains h m); SMTPat (contains h m'); SMTPat (addr_of m); SMTPat (addr_of m')]
  = ()

(* Select. *)

let sel #a #b h m =
  match snd h m with
  | Some (| _ , (x , _) |) -> x


(* Generating a fresh reference for the given heap. *)

let alloc_ref h a r x =
  (fst h , (fst h + 1 , (fun n -> if n = fst h then Some (| a , (x , r) |)
					       else snd h n)))


(* Update. *)

let upd #a #r h0 m x =
  (fst h0 , (fun m' -> if m = m' then Some (| a , (x , r) |)
                                 else snd h0 m'))


(* Empty. *)

let emp = 0, (fun (r:nat) -> None)
