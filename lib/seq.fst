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
module Seq

(* Representation hidden from clients *)
type seq (a:Type) = { 
  contents: nat -> Tot a;
  length:   nat
}

(* Primitive operations on sequences *)
let length s = s.length

let create len v = {
  contents=(fun i -> v);
  length=len;
}

let index s i = s.contents i

let upd s n v = {
  contents=(fun i -> if i=n then v else s.contents i);
  length=s.length;
}

let append s1 s2 = {
  contents=(fun x -> if x < s1.length then s1.contents x else s2.contents (x - s1.length));
  length=s1.length + s2.length;
}

let slice s i j = {
  contents=(fun x -> s.contents (x + i));
  length=j - i;
}

(* Lemmas about length *)
let lemma_create_len n i   = ()
let lemma_len_upd n v s    = ()
let lemma_len_append s1 s2 = ()
let lemma_len_slice s i j  = ()

(* Lemmas about index *)
let lemma_index_create n v i  = ()
let lemma_index_upd1 n v s    = ()
let lemma_index_upd2 n v s i  = ()
let lemma_index_app1 s1 s2 i  = ()
let lemma_index_app2 s2 s2 i  = ()
let lemma_index_slice s i j k = ()

logic type Eq: #a:Type -> seq a -> seq a -> Type = fun (a:Type) (s1:seq a) (s2:seq a) -> 
  (length s1 = length s2 
   /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i)))
(* Need to assume extensionality here, since it doesn't follow from functional extensionality alone; 
   We only want the maps that hold the sequences to agree on the locations within range;
   An alternative would be to define 

       type seq (a:Type) = (| len:nat * (x:nat{x < len} -> a) |)

   i.e., restricting the domain of the maps to the indices within range only. 
   In that case, functional extensionality should suffice.
 
   TODO: try moving to that style?
 *)
assume Extensionality: forall (a:Type) (s1:seq a) (s2:seq a). Eq s1 s2 <==> (s1=s2)

let lemma_eq_intro s1 s2 = ()
let lemma_eq_refl s1 s2  = ()
let lemma_eq_elim s1 s2  = ()
