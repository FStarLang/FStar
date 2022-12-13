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

unfold
let is_monotonic (#a:Type) (wp:pure_wp' a) =
  (*
   * Once we support using tactics in ulib/,
   *   this would be written as: Prims.pure_wp_monotonic0,
   *   with a postprocessing tactic to norm it
   *)
  forall (p q:pure_post a). (forall (x:a). p x ==> q x) ==> (wp p ==> wp q)  

let elim_pure_wp_monotonicity (#a:Type) (wp:pure_wp a)
  : Lemma (is_monotonic wp)
  = reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic

let elim_pure_wp_monotonicity_forall (_:unit)
  : Lemma
    (forall (a:Type) (wp:pure_wp a). is_monotonic wp)
  = reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic

let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires is_monotonic wp)
      (ensures pure_wp_monotonic a wp)
  = reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic

unfold
let as_pure_wp (#a:Type) (wp:pure_wp' a)
  : Pure (pure_wp a)
      (requires is_monotonic wp)
      (ensures fun r -> r == wp)
  = intro_pure_wp_monotonicity wp;
    wp

let elim_pure (#a:Type) (#wp:pure_wp a) ($f : unit -> PURE a wp) (p:pure_post a)
  : Pure a (requires (wp p)) (ensures (fun r -> p r))
  = elim_pure_wp_monotonicity wp;
    f ()
