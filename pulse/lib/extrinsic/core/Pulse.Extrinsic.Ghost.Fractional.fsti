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
module Pulse.Extrinsic.Ghost.Fractional

(** Fractional GHOST cells, using the existing Pulse fraction PCM.
    Compatible shares agree on their value and sum to at most one. Split
    preserves the value; writing requires the full share. Two thread-private
    halves can therefore record agreement with halves stored in an invariant.
    These rules do not authorize physical writes through fractional read
    permissions. Use an explicit #a when values have refined types: ownership
    at #int and at a refinement of int instantiates different PCMs. *)

open FStar.Real
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module G = Pulse.Extrinsic.Ghost

let fraction = p:PulseCore.FractionalPermission.perm{p <=. 1.0R}
val own (#a:Type0) (g:G.name) (p:fraction) (x:a) : S.slprop
let allocated (#a:Type0) (x:a) = S.op_exists_Star (fun (g:G.name) -> own g 1.0R x)

val alloc (#a:Type0) (mask:S.inames) (x:a)
  : Lemma (P.update mask mask S.emp (allocated x))
val split (#a:Type0) (g:G.name) (p:fraction) (q:fraction{p +. q <=. 1.0R}) (x:a)
  : Lemma (own g (p +. q) x == S.star (own g p x) (own g q x))
val agree (#a:Type0) (g:G.name) (p q:fraction) (x y:a)
  : Lemma (S.implies (S.star (own g p x) (own g q y))
      (S.pure (x == y /\ p +. q <=. 1.0R)))
val write (#a:Type0) (mask:S.inames) (g:G.name) (old desired:a)
  : Lemma (P.update mask mask (own g 1.0R old) (own g 1.0R desired))
val exposed (#a:Type0) (g:G.name) (p:fraction) (x:a)
  : Lemma (
      S.implies (P.exposed (own g p x)) (own g p x) /\
      S.implies (own g p x) (P.exposed (own g p x)))
