(*
   Copyright 2019-2021 Microsoft Research

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
module PulseCore.Semantics
(**
 * This module provides a semantic model for a combined effect of
 * divergence, state and parallel composition of atomic actions.
 *
 * It also builds a generic separation-logic-style program logic
 * for this effect, in a partial correctness setting.

 * It is also be possible to give a variant of this semantics for
 * total correctness. However, we specifically focus on partial correctness
 * here so that this semantics can be instantiated with lock operations,
 * which may deadlock. See ParTot.fst for a total-correctness variant of
 * these semantics.
 *
 *)

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quanitifers was more convenient for the proof done here.

let associative #a (f: a -> a -> a) =
  forall x y z. f x (f y z) == f (f x y) z

let commutative #a (f: a -> a -> a) =
  forall x y. f x y == f y x

let is_unit #a (x:a) (f:a -> a -> a) =
  forall y. f x y == y /\ f y x == y


(**
 * In addition to being a commutative monoid over the carrier [r]
 * a [comm_monoid s] also gives an interpretation of `r`
 * as a predicate on states [s]
 *)
noeq
type comm_monoid (s:Type u#s) : Type u#(s + 1) = {
  r:Type u#s;
  emp: r;
  star: r -> r -> r;
  interp: r -> s -> prop;
  laws: squash (associative star /\ commutative star /\ is_unit emp star)
}

(** [post a c] is a postcondition on [a]-typed result *)
let post #s a (c:comm_monoid s) = a -> c.r

(** [action c s]: atomic actions are, intuitively, single steps of
 *  computations interpreted as a [s -> a & s].
 *  However, we augment them with two features:
 *   1. they have pre-condition [pre] and post-condition [post]
 *   2. their type guarantees that they are frameable
 *  Thanks to Matt Parkinson for suggesting to set up atomic actions
 *  this way.
 *  Also see: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/views.pdf
 *)

noeq
type action (#s:Type u#s) (c:comm_monoid u#s s) (a:Type u#s) : Type u#s  = {
   pre: c.r;
   post: a -> c.r;
   sem: (frame:c.r ->
         s0:s{c.interp (c.star pre frame) s0} ->
         (x:a & s1:s{c.interp (post x `c.star` frame) s1}));
}

val m (#s:Type u#s) (#c:comm_monoid u#s s)
  : (a:Type u#a) -> c.r -> post a c -> Type u#(max (s + 1) (1 + a))

val return
    (#s:Type u#s)
    (#c:comm_monoid s)
    #a 
    (x:a)
    (post:a -> c.r)
: m a (post x) post

val act
    (#s:Type u#s)
    (#c:comm_monoid s)
    (#t:Type u#s)
    (a:action c t)
: m t a.pre a.post

val bind 
    (#s:Type u#s)
    (#c:comm_monoid s)
    (#a:Type u#a)
    (#b:Type u#b)
    (#p:c.r)
    (#q:a -> c.r)
    (#r:b -> c.r)
    (f:m a p q)
    (g: (x:a -> Dv (m b (q x) r)))
: Dv (m b p r)

val frame
    (#s:Type u#s)
    (#c:comm_monoid s)
    (#a:Type u#a)
    (#p:c.r)
    (#q:a -> c.r)
    (fr:c.r)
    (f:m a p q)
: Dv (m a (p `c.star` fr) (fun x -> q x `c.star` fr))

val par 
    #s (#c:comm_monoid s)
    #p0 #q0 (m0:m unit p0 (fun _ -> q0))
    #p1 #q1 (m1:m unit p1 (fun _ -> q1))
: Dv (m unit (p0 `c.star` p1) (fun _ -> q0 `c.star` q1))
