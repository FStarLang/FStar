(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.Guarded

(** Guarded fixed points of families of existing PulseCore assertions.
    Agreement below n is observational equivalence at smaller memory levels;
    contractiveness turns it into agreement below n+1. [fix] and [unfold_fix]
    expose the resulting fixed point without exposing level-indexed predicates.
    WP uses this interface to recurse through source steps, including loops
    and spawning, without recursion on program syntax. *)

module S = PulseCore.IndirectionTheorySep

let family (a:Type) = a -> S.slprop

val agrees_below (#a:Type) (n:nat) (p q:family a) : prop

let contractive (#a:Type) (f:family a -> family a) : prop =
  forall n p q. agrees_below n p q ==> agrees_below (n + 1) (f p) (f q)

let operator (a:Type) = f:(family a -> family a) { contractive f }

val fix (#a:Type) (f:operator a) : family a

val unfold_fix (#a:Type) (f:operator a) (x:a)
  : Lemma (fix f x == f (fix f) x)

val later_contractive (#a:Type) ()
  : Lemma (contractive (fun (p:family a) x -> S.later (p x)))
