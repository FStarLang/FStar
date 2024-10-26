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

val cinv_vp (c:cinv) (v:slprop) : slprop

val active (c:cinv) (p:perm) : slprop

val active_is_slprop2 (c:cinv) (p:perm)
  : Lemma (is_slprop2 (active c p))
          [SMTPat (is_slprop2 (active c p))]

val iname_of (c:cinv) : GTot iname

val new_cancellable_invariant (v:slprop)
  : stt_ghost cinv emp_inames
      v
      (fun c -> inv (iname_of c) (cinv_vp c v) ** active c 1.0R)

val unpacked (c:cinv) (v:slprop) : slprop

val unpack_cinv_vp (#p:perm) (#v:slprop) (c:cinv)
  : stt_ghost unit emp_inames
      (cinv_vp c v ** active c p)
      (fun _ -> v ** unpacked c v ** active c p)

val pack_cinv_vp (#v:slprop) (c:cinv)
  : stt_ghost unit emp_inames
      (v ** unpacked c v)
      (fun _ -> cinv_vp c v)

val share (#p:perm) (c:cinv)
  : stt_ghost unit emp_inames
      (active c p)
      (fun _ -> active c (p /. 2.0R) ** active c (p /. 2.0R))

val share2 (c:cinv)
  : stt_ghost unit emp_inames
      (active c 1.0R)
      (fun _ -> active c 0.5R ** active c 0.5R)

[@@allow_ambiguous]
val gather (#p1 #p2 :perm) (c:cinv)
  : stt_ghost unit emp_inames
      (active c p1 ** active c p2)
      (fun _ -> active c (p1 +. p2))

[@@allow_ambiguous]
val gather2 (c:cinv)
  : stt_ghost unit emp_inames
      (active c 0.5R ** active c 0.5R)
      (fun _ -> active c 1.0R)

val cancel (#v:slprop) (c:cinv)
  : stt_ghost unit (add_inv emp_inames (iname_of c))
      (inv (iname_of c) (cinv_vp c v) ** active c 1.0R ** later_credit 1)
      (fun _ -> v)
