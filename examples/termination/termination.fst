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

val ack_swap: n:nat -> m:nat -> Tot nat (decreases %[m;n])
let rec ack_swap n m =
  if m=0 then n + 1
  else if n = 0 then ack_swap 1 (m - 1)
  else ack_swap (ack_swap (n - 1) m) (m - 1)

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _::tl -> 1 + length tl

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

(* map and treemap *)

val map : f:('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f l = match l with
  | [] -> []
  | hd::tl -> f hd::map f tl

val mem: #a:eqtype -> x:a -> list a -> Tot bool
let rec mem #a x l = match l with
  | [] -> false
  | hd::tl ->
    hd=x || mem x tl

val list_subterm_ordering_coercion: 
			  #a:eqtype 
			-> #b:Type
			-> l:list a
                        -> bound:b{l << bound}
                        -> Tot (m:list a{l==m /\ (forall (x:a). mem x m ==> x << bound)})
let rec list_subterm_ordering_coercion #a #b l bound = match l with
  | [] -> []
  | hd::tl ->
    hd::list_subterm_ordering_coercion tl bound

(* WARNING: pattern does not contain all quantified variables. *)
val list_subterm_ordering_lemma:
			#a:eqtype
			-> #b:Type
			-> l:list a
                        -> bound:b
                        -> x:a
                        -> Lemma (requires (l << bound))
                                 (ensures (mem x l ==> x << bound))
                                 [SMTPat (mem x l);
                                  SMTPat (x << bound)]
let rec list_subterm_ordering_lemma #a #b l bound x = match l with
  | [] -> ()
  | hd::tl -> list_subterm_ordering_lemma tl bound x

val move_refinement:  #a:eqtype
                   -> #p:(a -> Type)
                   -> l:list a{forall z. mem z l ==> p z}
                   -> Tot (list (x:a{p x}))
let rec move_refinement #a #p l = match l with
  | [] -> []
  | hd::tl -> hd::move_refinement #a #p tl

type tree (a:Type) =
  | Leaf : a -> tree a
  | Node : list (tree a) -> tree a

val treeMap : #a:eqtype -> #b:Type -> (a -> Tot b) -> tree a -> Tot (tree b)
let rec treeMap #a #b f v = match v with
  | Leaf a -> Leaf (f a)
  | Node l ->
    (* NS: this next call seems to be unavoidable. We need to move the refinement "inside" the list.
           An alternative would be to give map a different type accounting for this "outside" refinement.
           But, it seems nicer to give map its normal type *)
    let l = move_refinement #_ #(fun aa -> aa << v) l in (* ghost *)
    Node (map (treeMap f) l) //treeMap f: (x:T a{x << v} -> Tot (T b))

(* CH: The problem I see with Nik's trick is that adding "ghost" in a
       comment: doesn't make something Ghost in F*, and in fact
       `move_refinement` has a significant computational cost. *)

(* CH: here is the variant in which map gets a different type: *)

let rec list_map (xs:list 'a) (f:(x:'a{x<<xs} -> 'b)) : list 'b =
  match xs with
  | [] -> []
  | x::xs' -> f x :: list_map xs' f

let rec tree_map (f:'a -> 'b) (t:tree 'a) : tree 'b =
  match t with
  | Leaf v -> Leaf (f v)
  | Node ts -> Node (list_map ts (tree_map f))

(* CH: here is a very similar example that came up in a mailing list discussion:
       https://lists.gforge.inria.fr/pipermail/fstar-club/2017/000078.html *)

let rec flatten_list (#a #b:Type) (l:(list b)) (f:(b -> list a)) : list a =
  match l with
  | []    -> []
  | hd::tl -> FStar.List.append (f hd) (flatten_list tl f)

(* solution #1 *)

let rec flatten_tree (#a:eqtype) (t:tree a) : list a =
  match t with
  | Leaf v -> [v]
  | Node l -> let l = move_refinement #_ #(fun aa -> aa << t) l in
              flatten_list l flatten_tree

(* solution #2 *)

let rec flatten_list' (l:(list 'b)) (f:(x:'b{x << l} -> list 'a)) : list 'a =
  match l with
  | []    -> []
  | hd::tl -> FStar.List.append (f hd) (flatten_list' tl f)

let rec flatten_tree' (#a:Type) (t:tree a) : list a =
  match t with
  | Leaf v -> [v]
  | Node l -> flatten_list' l flatten_tree'
