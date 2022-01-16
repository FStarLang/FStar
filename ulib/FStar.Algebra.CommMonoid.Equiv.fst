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
module FStar.Algebra.CommMonoid.Equiv

open FStar.Mul

unopteq
type equiv (a:Type) =
  | EQ :
    eq:(a -> a -> Type0) -> 
    reflexivity:(x:a -> Lemma (x `eq` x)) ->
    symmetry:(x:a -> y:a -> Lemma (requires (x `eq` y)) (ensures (y `eq` x))) ->
    transitivity:(x:a -> y:a -> z:a -> Lemma (requires (x `eq` y /\ y `eq` z)) (ensures (x `eq` z))) ->
    equiv a

let elim_eq_laws #a (eq:equiv a)
  : Lemma (
          (forall x.{:pattern (x `eq.eq` x)} x `eq.eq` x) /\
          (forall x y.{:pattern (x `eq.eq` y)} x `eq.eq` y ==> y `eq.eq` x) /\
          (forall x y z.{:pattern eq.eq x y; eq.eq y z} (x `eq.eq` y /\ y `eq.eq` z) ==> x `eq.eq` z)
          )
  = introduce forall x. x `eq.eq` x
    with (eq.reflexivity x);

    introduce forall x y. x `eq.eq` y ==> y `eq.eq` x
    with (introduce _ ==> _
          with _. eq.symmetry x y);

    introduce forall x y z. (x `eq.eq` y /\ y `eq.eq` z) ==> x `eq.eq` z
    with (introduce _ ==> _
          with _. eq.transitivity x y z)

let equality_equiv (a:Type) : equiv a =
  EQ (fun x y -> x == y) (fun x -> ()) (fun x y -> ()) (fun x y z -> ())

unopteq
type cm (a:Type) (eq:equiv a) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    identity : (x:a -> Lemma ((unit `mult` x) `EQ?.eq eq` x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma ((x `mult` y `mult` z) `EQ?.eq eq` (x `mult` (y `mult` z)))) ->
    commutativity:(x:a -> y:a -> Lemma ((x `mult` y) `EQ?.eq eq` (y `mult` x))) ->
    congruence:(x:a -> y:a -> z:a -> w:a -> Lemma (requires (x `EQ?.eq eq` z /\ y `EQ?.eq eq` w)) (ensures ((mult x y) `EQ?.eq eq` (mult z w)))) ->
    cm a eq



// temporarily fixing the universe of this lemma to u#1 because 
// otherwise tactics for LowStar.Resource canonicalization fails
// by picking up an incorrect universe u#0 for resource type
let right_identity (#a:Type u#aa) (eq:equiv a) (m:cm a eq) (x:a)
  : Lemma (x `CM?.mult m` (CM?.unit m) `EQ?.eq eq` x) = 
  CM?.commutativity m x (CM?.unit m); 
  CM?.identity m x;
  EQ?.transitivity eq (x `CM?.mult m` (CM?.unit m)) ((CM?.unit m) `CM?.mult m` x) x

let int_plus_cm : cm int (equality_equiv int) =
  CM 0 (+) (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ()) (fun _ _ _ _ -> ())

let int_multiply_cm : cm int (equality_equiv int) =
  CM 1 ( * ) (fun _ -> ()) (fun _ _ _ -> ()) (fun _ _ -> ()) (fun _ _ _ _ -> ())
