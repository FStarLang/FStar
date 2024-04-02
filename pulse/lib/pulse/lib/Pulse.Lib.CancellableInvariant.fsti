(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.CancellableInvariant

open Pulse.Lib.Pervasives

[@@ erasable]
val token : Type0

val cancellable (t:token) (v:vprop) : vprop

val cancellable_big (t:token) (v:vprop)
  : Lemma (is_big v ==> is_big (cancellable t v))

val active (p:perm) (t:token) : vprop

val taken (t:token) : vprop

[@@ erasable]
noeq
type cinv =
  | E : i:iref -> t:token -> cinv

instance val non_informative_cinv
  : NonInformative.non_informative cinv

val new_cancellable_invariant (v:vprop { is_big v })
  : stt_ghost cinv emp_inames
      v
      (fun r -> inv r.i (cancellable r.t v) ** active full_perm r.t)

val take (#p:perm) (#v:vprop) (t:token)
  : stt_ghost unit emp_inames
      (cancellable t v ** active p t)
      (fun _ -> v ** active p t ** taken t)

val give (#v:vprop) (t:token)
  : stt_ghost unit emp_inames
      (v ** taken t)
      (fun _ -> cancellable t v)

val share (#p:perm) (t:token)
  : stt_ghost unit emp_inames
      (active p t)
      (fun _ -> active (half_perm p) t ** active (half_perm p) t)

val gather (#p:perm) (t:token)
  : stt_ghost unit emp_inames
      (active (half_perm p) t ** active (half_perm p) t)
      (fun _ -> active p t)

val cancel (#v:vprop) (i:cinv)
  : stt_ghost unit (add_inv emp_inames i.i)
      (inv i.i (cancellable i.t v) ** active full_perm i.t)
      (fun _ -> v)



// r:ref bool
// inv_p = exists b. pts_to r full_perm b **
//                   (if b then p else emp)
// inv i inv_p

// to allow for release predicate:

// add a ghost ref that mirrors the concrete ref
// and half give to the user when locked, half in the inv, else full in the inv

// now for sharing etc.:

