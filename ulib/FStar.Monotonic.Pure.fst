(*
   Copyright 2019 Microsoft Research

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

module FStar.Monotonic.Pure

(*
 * This module provides utilities to intro and elim the monotonicity
 *   property of pure wps
 *
 * Since pure_wp_monotonic predicate is marked opaque_to_smt in prims,
 *   reasoning with it requires explicit coercions
 *)

let elim_pure_wp_monotonicity (#a:Type) (wp:pure_wp a)
  : Lemma (forall (p q:pure_post a). (forall (x:a). p x ==> q x) ==> (wp p ==> wp q))
  = reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic

let elim_pure_wp_monotonicity_forall (_:unit)
  : Lemma
    (forall (a:Type) (wp:pure_wp a). (forall (p q:pure_post a).
       (forall (x:a). p x ==> q x) ==> (wp p ==> wp q)))
  = reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic

let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires forall (p q:pure_post a). (forall (x:a). p x ==> q x) ==> (wp p ==> wp q))
      (ensures pure_wp_monotonic a wp)
  = reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic

unfold
let coerce_to_pure_wp (#a:Type) (wp:pure_wp' a)
  : Pure (pure_wp a)
      (requires forall (p q:pure_post a). (forall (x:a). p x ==> q x) ==> (wp p ==> wp q))
      (ensures fun r -> r == wp)
  = intro_pure_wp_monotonicity wp;
    wp
