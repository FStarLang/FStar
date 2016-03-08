(*
   Copyright 2008-2015 Nikhil Swamy and Microsoft Research

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

(*
   This development shows how to derive a Dijkstra state monad,
      Deriving.ST.WP    (shortened within this module to just WP)
   from a pre-existing Dijkstra monad of pure computations,
      Prims.PureWP

   The basic idea is to use define a computation type
      DST (a:Type) (wp:WP a)
   using the function type
      m:mem -> PURE (a * mem) (wp m: PureWP (a * mem))

   I.e,. this is the usual implementation of the state monad as a
   state-passing function

   Then, using the given semantics of PureWP, we can just compute
   the definitions of the usual monadic combinators for Deriving.ST.WP. We
   also prove that the resulting construction satisfies the expected monad laws.
*)
module Deriving.ST
(* An abbreviation P, for the PURE computation type (ignoring WLPs for now) *)
effect P (a:Type) (wp:PureWP a) = PURE a wp wp

(* The signature of the to-be-constructed Dijkstra state monad *)
kind Pre (mem:Type)           = mem -> Type
kind Post (mem:Type) (a:Type) = (a * mem) -> Type
kind WP (mem:Type) (a:Type)   = Post mem a -> Pre mem

(* A new computation type *)
type DST (mem:Type) (a:Type) (wp:WP mem a) = m0:mem -> P (a * mem) (fun 'p -> wp 'p m0)

(* We need a monotonicity condition for WP, defined below
   Question: Is there a systematic way to derive the definition
             of monotonic_WP from the definition of monotonic_PureWP?
*)
opaque type implies_ST (#a:Type) (#mem:Type) (p1:Post mem a) (p2:Post mem a) =
  forall x m. p1 (x, m) ==> p2 (x, m)
opaque type monotone_WP (#a:Type) (#mem:Type) (wp:WP mem a) =
      forall (p1:Post mem a) (p2:Post mem a).{:pattern (wp p1); (wp p2)}
                implies_ST p1 p2
                ==> (forall m. wp p1 m ==> wp p2 m)

(* A couple of tests to check that simple monotonicity properties are provable *)
val test_monotone1: #mem:Type -> #a:Type -> wp:WP mem a -> m0:mem
  -> Lemma (requires (monotone_WP wp /\ wp (fun xm -> m0 == snd xm) m0))
           (ensures (wp (fun xm -> True) m0))
let test_monotone1 (mem:Type) (a:Type) (wp:WP mem a) (m0:mem) = ()

val test_monotone2: #mem:Type -> #a:Type -> wp:WP mem a -> m0:mem -> p:Type -> q:Type
  -> Lemma (requires (monotone_WP wp /\ wp (fun xm -> p /\ q) m0))
           (ensures (wp (fun xm -> p) m0))
let test_monotone2 (mem:Type) (a:Type) (wp:WP mem a) (m0:mem) (p:Type) (q:Type) = ()

(* The return (aka unit) of WP *)
type wp_return (#mem:Type) (#a:Type) (x:a) (post:Post mem a) (m0:mem) = post (x, m0)
val return : #mem:Type -> #a:Type -> x:a -> Tot (DST mem a (wp_return x))
//we simply implement it as a pure function, and prove that it has the type wp_return
let return x m0 = (x, m0)

(* The bind of WP *)
type wp_bind (#mem:Type) (#a:Type) (#b:Type) (f:WP mem a) (g: a -> WP mem b) =
  fun (post:(b * mem) -> Type) (m0:mem) -> f (fun a_m1 -> g (fst a_m1) post (snd a_m1)) m0
val bind :   #mem:Type -> #a:Type -> #b:Type
            -> #wp1:WP mem a -> #wp2:(a -> WP mem b)
            -> f:DST mem a wp1{monotone_WP wp1 /\ (forall x. monotone_WP (wp2 x))}
            -> g: (x:a -> Tot (DST mem b (wp2 x)))
            -> Tot (DST mem b (wp_bind wp1 wp2))
//we implement it as the pure state-passing function; and prove that it satisfies wp_bind
let bind f g m0 = let xm1 = f m0 in g (fst xm1) (snd xm1)

(* Next, we prove two monotonicity properties of the construction *)
val lemma_return_monotone: mem:Type -> a:Type -> x:a -> Lemma (monotone_WP (wp_return #mem #a x))
let lemma_return_monotone x = ()

val lemma_bind_preserves_monotonicity: mem:Type -> a:Type -> b:Type -> wp1:WP mem a -> wp2:(a -> WP mem b)
                  -> Lemma (requires (monotone_WP wp1 /\ (forall x. monotone_WP (wp2 x))))
                           (ensures (monotone_WP (wp_bind wp1 wp2)))
let lemma_bind_preserves_monotonicity (mem:Type) (a:Type) (b:Type) (wp1:WP mem a) (wp2:a -> WP mem b) = ()

(* And here are proofs of the three monad laws *)
val lemma_bind_assoc: mem:Type -> a:Type -> b:Type -> c:Type
                  -> wp1: WP mem a
                  -> wp2: (a -> WP mem b)
                  -> wp3: (b -> WP mem c)
                  -> Lemma (forall (post:Post mem c) (m0:mem).
                                wp_bind wp1 (fun x -> wp_bind (wp2 x) wp3) post m0
                                <==>
                                wp_bind (wp_bind wp1 wp2) wp3 post m0)
let lemma_bind_assoc (mem:Type) (a:Type) (b:Type) (c:Type)
                     (wp1:WP mem a) (wp2: a -> WP mem b) (wp3: b -> WP mem c) = () (* easy, just computation *)

val lemma_left_unit: mem:Type -> a:Type -> b:Type
                  -> x:a
                  -> wp2:(a -> WP mem b)
                  -> Lemma (forall (post:Post mem b) (m0:mem).
                                   wp_bind (wp_return x) wp2 post m0
                                   <==>
                                   wp2 x post m0)
let lemma_left_unit (mem:Type) (a:Type) (b:Type) (x:a) (wp2: a -> WP mem b) = () (* also easy, just computation *)

val lemma_right_unit: mem:Type -> a:Type
                   -> wp1:WP mem a
                   -> Lemma (requires (monotone_WP wp1))
                            (ensures (forall (post:Post mem a) (m0:mem).
                                         wp_bind wp1 (wp_return #mem #a) post m0
                                         <==>
                                         wp1 post m0))
let lemma_right_unit (mem:Type) (a:Type) (wp1:WP mem a) = () (* a little bit of logical reasoning with monotonicity *)

(* Finally, we define a lifting from PureWP to WP, and prove that it is a morphism *)
(* First, we need a notion of monotonicity for PureWP *)
opaque type monotone_PureWP (#a:Type) (wp:PureWP a) =
   (forall (p1:PurePost a) (p2:PurePost a).{:pattern (wp p1); (wp p2)}
           (forall x. p1 x ==> p2 x)
        ==> (wp p1 ==> wp p2))

(* Here's the lift from Pure to ST *)
type wp_lift (#mem:Type) (#a:Type) (wp:PureWP a) : WP mem a = (fun (post:Post mem a) (m0:mem) -> wp (fun x -> post (x, m0)))
val lift: mem:Type -> a:Type -> wp:PureWP a -> f:(unit -> P a wp){monotone_PureWP wp} -> Tot (DST mem a (wp_lift wp))
let lift 'mem 'a 'wp f m0 = f(), m0

(* We prove the two morphism laws *)
val lift_unit: #mem:Type -> #a:Type -> x:a -> p:Post mem a -> m0:mem
  -> Lemma (wp_return x p m0 <==> wp_lift (pure_return a x) p m0)
let lift_unit 'mem 'a x 'p m0 = ()

val lemma_lift_bind: mem:Type -> a:Type -> b:Type
                  -> wp1: PureWP a
                  -> wp2: (a -> PureWP b)
                  -> post:Post mem b
                  -> m0:mem
                  -> Lemma
    (requires (monotone_PureWP wp1 /\ (forall x. monotone_PureWP (wp2 x))))
    (ensures  (wp_bind (wp_lift wp1) (fun x -> wp_lift (wp2 x)) post m0
               <==>
               wp_lift (pure_bind_wlp a b wp1 wp2) post m0))
let lemma_lift_bind 'mem 'a 'b 'wp1 'wp2 'post m0 = ()
