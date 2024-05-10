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
val cinv : Type0

instance val non_informative_cinv
  : NonInformative.non_informative cinv

val cinv_vp (c:cinv) (v:vprop) : vprop

val is_big_cinv_vp (c:cinv) (v:vprop)
  : Lemma (is_big v ==> is_big (cinv_vp c v))

val active (p:perm) (c:cinv) : vprop

val active_is_small (p:perm) (c:cinv)
  : Lemma (is_small (active p c))
          [SMTPat (is_small (active p c))]

val iref_of (c:cinv) : GTot iref

val new_cancellable_invariant (v:vprop { is_big v })
  : stt_ghost cinv emp_inames
      v
      (fun c -> inv (iref_of c) (cinv_vp c v) ** active 1.0R c)

val unpacked (c:cinv) : vprop

val unpack_cinv_vp (#p:perm) (#v:vprop) (c:cinv)
  : stt_ghost unit emp_inames
      (cinv_vp c v ** active p c)
      (fun _ -> v ** unpacked c ** active p c)

val pack_cinv_vp (#v:vprop) (c:cinv)
  : stt_ghost unit emp_inames
      (v ** unpacked c)
      (fun _ -> cinv_vp c v)

val share (#p:perm) (c:cinv)
  : stt_ghost unit emp_inames
      (active p c)
      (fun _ -> active (p /. 2.0R) c ** active (p /. 2.0R) c)

val share2 (c:cinv)
  : stt_ghost unit emp_inames
      (active 1.0R c)
      (fun _ -> active 0.5R c ** active 0.5R c)

val gather (#p1 #p2 :perm) (c:cinv)
  : stt_ghost unit emp_inames
      (active p1 c ** active p2 c)
      (fun _ -> active (p1 +. p2) c)

val gather2 (c:cinv)
  : stt_ghost unit emp_inames
      (active 0.5R c ** active 0.5R c)
      (fun _ -> active 1.0R c)

val cancel (#v:vprop) (c:cinv)
  : stt_ghost unit (add_inv emp_inames (iref_of c))
      (inv (iref_of c) (cinv_vp c v) ** active 1.0R c)
      (fun _ -> v)
