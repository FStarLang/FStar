(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.ReflexiveTransitiveClosure

/// This module defines the reflexive transitive closure of a
/// relation. That is, the smallest preorder that includes it.
///
/// Closures are convenient for defining monotonic memory references:
///
/// - Define a `step` relation and take `closure step` as the
///   monotonic relation of the reference.
///
/// - To witness a property of the value of the reference, one must
///   show that the property is stable with respect to `closure step`,
///   but this boils down to proving that is stable with respect to
///   `step` (see lemma `stable_on_closure` below).
///
/// See examples/preorder/Closure.fst for usage examples.

let binrel (a:Type) = a -> a -> Type

let predicate (a:Type u#a) = a -> Type0

let reflexive (#a:Type) (rel:binrel u#a u#r a) =
  forall (x:a). squash (rel x x)

let transitive (#a:Type) (rel:binrel u#a u#r a) =
  forall (x:a) (y:a) (z:a). (squash (rel x y) /\ squash (rel y z)) ==> squash (rel x z)

let preorder_rel (#a:Type) (rel:binrel u#a u#r a) =
  reflexive rel /\ transitive rel

type preorder (a:Type u#a) : Type u#(max a (1 + r)) = rel:binrel u#a u#r a{preorder_rel rel}

let stable (#a:Type u#a) (p:a -> Type0) (rel:binrel u#a u#r a{preorder_rel rel}) =
  forall (x:a) (y:a). (p x /\ squash (rel x y)) ==> p y

val closure (#a:Type u#a) (r:binrel u#a u#r a) : preorder u#a u#0 a

(** `closure r` includes `r` *)
val closure_step: #a:Type u#a -> r:binrel u#a u#r a -> x:a -> y:a { r x y }
  -> Lemma (ensures closure r x y)
    [SMTPat (closure r x y)]

(** `closure r` is the smallest preorder that includes `r` *)
val closure_inversion: #a:Type u#a -> r:binrel u#a u#r a -> x:a -> y:a
  -> Lemma (requires closure r x y)
          (ensures  x == y \/ (exists z. squash (r x z) /\ closure r z y))

(**
* A predicate that is stable on `r` is stable on `closure r`
*
* This is useful to witness properties of monotonic references where
* the monotonicity relation is the closure of a step relation.
*)
val stable_on_closure: #a:Type u#a -> r:binrel u#a u#r a -> p:(a -> Type0)
  -> p_stable_on_r: (squash (forall x y.{:pattern (p y); (r x y)} p x /\ squash (r x y) ==> p y))
  -> Lemma (forall x y.{:pattern (closure r x y)} p x /\ closure r x y ==> p y)
