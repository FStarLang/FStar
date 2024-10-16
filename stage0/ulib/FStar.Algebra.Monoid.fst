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
module FStar.Algebra.Monoid

open FStar.Classical
module PropExt = FStar.PropositionalExtensionality

(*
 * AR: 05/12: adding calls to equational lemmas from PropositionalExtensionality
 *            these should go away with proper prop support
 *            also see the comment in PropositionalExtensionality.fst
 *)

(** Definition of a monoid *)

let right_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). x `mult` u == x

let left_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). u `mult` x == x

let associativity_lemma (m:Type) (mult:m -> m -> m) =
  forall (x y z:m). x `mult` y `mult` z == x `mult` (y `mult` z)

unopteq
type monoid (m:Type) =
  | Monoid :
    unit:m ->
    mult:(m -> m -> m) ->
    right_unitality:squash (right_unitality_lemma m unit mult) ->
    left_unitality:squash (left_unitality_lemma m unit mult) ->
    associativity:squash (associativity_lemma m mult) ->
    monoid m


let intro_monoid (m:Type) (u:m) (mult:m -> m -> m)
  : Pure (monoid m)
    (requires (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult))
=
  Monoid u mult () () ()


(** Some monoid structures *)

let nat_plus_monoid : monoid nat =
  let add (x y : nat) : nat = x + y in
  intro_monoid nat 0 add

let int_plus_monoid : monoid int =
  intro_monoid int 0 (+)

(* let int_mul_monoid : monoid int = *)
(*   intro_monoid int 1 op_Multiply *)

let conjunction_monoid : monoid prop =
  let u : prop = singleton True in
  let mult (p q : prop) : prop = p /\ q in

  let left_unitality_helper (p:prop) : Lemma ((u `mult` p) == p) =
    assert ((u `mult` p) <==> p) ;
    PropExt.apply (u `mult` p) p
  in

  let right_unitality_helper (p:prop) : Lemma ((p `mult` u) == p) =
    assert ((p `mult` u) <==> p) ;
    PropExt.apply (p `mult` u) p
  in

  let associativity_helper (p1 p2 p3 : prop) : Lemma (p1 `mult` p2 `mult` p3 == p1 `mult` (p2 `mult` p3)) =
    assert (p1 `mult` p2 `mult` p3 <==> p1 `mult` (p2 `mult` p3)) ;
    PropExt.apply (p1 `mult` p2 `mult` p3) (p1 `mult` (p2 `mult` p3))
  in

  forall_intro right_unitality_helper ;
  assert (right_unitality_lemma prop u mult) ;
  forall_intro left_unitality_helper ;
  assert (left_unitality_lemma prop u mult) ;
  forall_intro_3 associativity_helper;
  assert (associativity_lemma prop mult) ;
  intro_monoid prop u mult


let disjunction_monoid : monoid prop =
  let u : prop = singleton False in
  let mult (p q : prop) : prop = p \/ q in

  let left_unitality_helper (p:prop) : Lemma ((u `mult` p) == p) =
    assert ((u `mult` p) <==> p) ;
    PropExt.apply (u `mult` p) p
  in

  let right_unitality_helper (p:prop) : Lemma ((p `mult` u) == p) =
    assert ((p `mult` u) <==> p) ;
    PropExt.apply (p `mult` u) p
  in

  let associativity_helper (p1 p2 p3 : prop) : Lemma (p1 `mult` p2 `mult` p3 == p1 `mult` (p2 `mult` p3)) =
    assert (p1 `mult` p2 `mult` p3 <==> p1 `mult` (p2 `mult` p3)) ;
    PropExt.apply (p1 `mult` p2 `mult` p3) (p1 `mult` (p2 `mult` p3))
  in

  forall_intro right_unitality_helper ;
  assert (right_unitality_lemma prop u mult) ;
  forall_intro left_unitality_helper ;
  assert (left_unitality_lemma prop u mult) ;
  forall_intro_3 associativity_helper;
  assert (associativity_lemma prop mult) ;
  intro_monoid prop u mult

let bool_and_monoid : monoid bool =
  let and_ b1 b2 = b1 && b2 in
  intro_monoid bool true and_

let bool_or_monoid : monoid bool =
  let or_ b1 b2 = b1 || b2 in
  intro_monoid bool false or_

let bool_xor_monoid : monoid bool =
  let xor b1 b2 = (b1 || b2) && not (b1 && b2) in
  intro_monoid bool false xor

let lift_monoid_option (#a:Type) (m:monoid a) : monoid (option a) =
  let mult (x y:option a) =
    match x, y with
    | Some x0, Some y0 -> Some (m.mult x0 y0)
    | _, _ -> None
  in
  intro_monoid (option a) (Some m.unit) mult

(* Definition of a morphism of monoid *)

let monoid_morphism_unit_lemma (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b) =
  f (Monoid?.unit ma) == Monoid?.unit mb

let monoid_morphism_mult_lemma (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b) =
  forall (x y:a). Monoid?.mult mb (f x) (f y) == f (Monoid?.mult ma x y)

type monoid_morphism (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b) =
  | MonoidMorphism :
    unit:squash (monoid_morphism_unit_lemma f ma mb) ->
    mult:squash (monoid_morphism_mult_lemma f ma mb) ->
    monoid_morphism f ma mb

let intro_monoid_morphism (#a #b:Type) (f:a -> b) (ma:monoid a) (mb:monoid b)
  : Pure (monoid_morphism f ma mb)
    (requires (monoid_morphism_unit_lemma f ma mb /\ monoid_morphism_mult_lemma f ma mb))
    (ensures (fun _ -> True))
=
  MonoidMorphism () ()

let embed_nat_int (n:nat) : int = n
let _ = intro_monoid_morphism embed_nat_int nat_plus_monoid int_plus_monoid

let neg (p:prop) : prop = ~p
let _ =
  assert (neg True <==> False) ;
  PropExt.apply (neg True) False ;
  let mult_lemma_helper (p q:prop) : Lemma (neg (p /\ q) == (neg p \/ neg q)) =
    assert (neg (p /\ q) <==> (neg p \/ neg q)) ;
    PropExt.apply (neg (p /\ q)) (neg p \/ neg q)
  in
  forall_intro_2 mult_lemma_helper ;
  intro_monoid_morphism neg conjunction_monoid disjunction_monoid

let _ =
  assert (neg False <==> True) ;
  PropExt.apply (neg False) True ;
  let mult_lemma_helper (p q:prop) : Lemma (neg (p \/ q) == (neg p /\ neg q)) =
    assert (neg (p \/ q) <==> (neg p /\ neg q)) ;
    PropExt.apply (neg (p \/ q)) (neg p /\ neg q)
  in
  forall_intro_2 mult_lemma_helper ;
  intro_monoid_morphism neg disjunction_monoid conjunction_monoid

(* Definition of a left action *)

let mult_act_lemma (m a:Type) (mult:m -> m -> m) (act:m -> a -> a) =
  forall (x x':m) (y:a). (x `mult` x') `act` y == x `act` (x' `act` y)

let unit_act_lemma (m a:Type) (u:m) (act:m -> a -> a) =
  forall (y:a). u `act` y == y

unopteq
type left_action (#m:Type) (mm:monoid m) (a:Type) =
  | LAct :
    act:(m -> a -> a) ->
    mult_lemma: squash (mult_act_lemma m a (Monoid?.mult mm) act) ->
    unit_lemma: squash (unit_act_lemma m a (Monoid?.unit mm) act) ->
    left_action mm a

let left_action_morphism
    (#a #b #ma #mb:Type)
    (f:a -> b)
    (* mf ought to be a monoid morphism but we don't use this fact in the property *)
    (mf: ma -> mb)
    (#mma:monoid ma)
    (#mmb:monoid mb)
    (la:left_action mma a)
    (lb:left_action mmb b)
= forall (g:ma) (x:a). LAct?.act lb (mf g) (f x) == f (LAct?.act la g x)
