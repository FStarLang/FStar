(* Expect 3 intentional failures *)

(*
   Copyright 2008-2014 Nikhil Swamy, Chantal Keller, Microsoft Research and Inria

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
module Termination

val factorial: nat -> Tot nat
let rec factorial x =
  match x with
    | 0 -> 1
    | _ -> (x + factorial (x - 1))

val fibonacci: nat -> Tot nat
let rec fibonacci n =
  if n<=1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

val ackermann: m:nat -> n:nat -> Tot nat
let rec ackermann m n =
  if m=0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

val ackermann_bad: m:int -> n:int -> Tot int
let rec ackermann_bad m n = (* expected failure *)
  if m=0 then n + 1
  else if n = 0 then ackermann_bad (m - 1) 1
  else ackermann_bad (m - 1) (ackermann_bad m (n - 1))

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _::tl -> 1 + length tl

val length_bad: list 'a -> Tot nat
let rec length_bad l = match l with (* expect failure *)
  | [] -> 0
  | _::tl -> 1 + length_bad l

val half_length: list 'a -> Tot nat
let rec half_length l = match l with
  | [] -> 0
  | [_] -> 0
  | _::_::tl -> 1 + half_length tl (* testing transitivity of ordering *)


(***** Coq-Club example *****)
val sumto: i:nat -> f:(x:nat{x <= i} -> Tot nat) -> Tot nat
let rec sumto i f =
  if i = 0
  then f 0
  else f i + sumto (i-1) f

val strangeZero: nat -> Tot nat
let rec strangeZero v =
  if v = 0
  then 0
  else sumto (v-1) strangeZero

val strangeZeroBad: nat -> Tot nat
let rec strangeZeroBad v = (* expect failure *)
  if v = 0
  then 0
  else sumto v strangeZeroBad

(* map and treemap *)

val map : ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f l = match l with
  | [] -> []
  | hd::tl -> f hd::map f tl

val mem: 'a -> list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

(* TODO: Writing the spec with refinements fails *)
(* val list_subterm_ordering: l:list 'a  *)
(*                         -> bound:'b{Precedes l bound} *)
(*                         -> Tot (m:list 'a{l==m /\ (forall (x:'a). mem x m ==> Precedes x bound)}) *)
val list_subterm_ordering_coercion: l:list 'a
                        -> bound:'b
                        -> Pure (list 'a)
                                (requires (Precedes l bound))
                                (ensures \m => (forall (x:'a). mem x m ==> Precedes x bound) /\ l==m)
let rec list_subterm_ordering_coercion l bound = match l with
  | [] -> l (* TODO: writing [] here causes it to fail because the [] doesn't appear in the VC *)
  | hd::tl ->
    let tl' = list_subterm_ordering_coercion tl bound in (* TODO: without the eplicit let-binding, this fails *)
    hd::tl'

val list_subterm_ordering_lemma: l:list 'a 
                        -> bound:'b
                        -> Pure unit
                                (requires (Precedes l bound))
                                (ensures \m => (forall (x:'a). mem x l ==> Precedes x bound))
let rec list_subterm_ordering_lemma l bound = match l with
  | [] -> () 
  | hd::tl -> list_subterm_ordering_lemma tl bound
      
val move_refinement: 'a:Type
                   -> 'P:('a => Type)
                   -> l:list 'a{forall z. mem z l ==> 'P z}
                   -> Tot (list (a:'a{'P a}))
let rec move_refinement 'a 'P l = match l with
  | [] -> []
  | hd::tl -> hd::(move_refinement 'a 'P tl)

type T 'a =
  | Leaf : 'a -> T 'a
  | Node : list (T 'a) -> T 'a

val treeMap : 'a:Type -> 'b:Type -> ('a -> Tot 'b) -> T 'a -> Tot (T 'b)
let rec treeMap 'a 'b f v = match v with
  | Leaf a -> Leaf (f a)
  | Node l ->
    let _ = (* ghost *) list_subterm_ordering_lemma l v in (* TODO: eliminate this explicit call by encoding the lemma to the solver *)
    (* NS: this next call seems to be unavoidable. We need to move the refinement "inside" the list. 
           An alternative would be to give map a different type accouting for this "outside" refinement. 
           But, it's seeems nicer to give map its normal type *)
    let l = (* ghost *) move_refinement (T 'a) (fun aa => Precedes (LexPair f (LexPair aa LexTop)) (LexPair f (LexPair v LexTop))) l in
    Node (map (treeMap f) l)
