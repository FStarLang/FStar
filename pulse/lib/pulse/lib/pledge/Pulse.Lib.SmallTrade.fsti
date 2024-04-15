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

module Pulse.Lib.SmallTrade

open Pulse.Lib.Core
open Pulse.Lib.InvList

module T = FStar.Tactics

val trade :
  (#[T.exact (`[])] is:invlist) ->
  (hyp:vprop) ->
  (concl:vprop) ->
  vprop

val trade_is_small (#is:invlist) (hyp concl:vprop)
  : Lemma (is_small (trade #is hyp concl))

val intro_trade
  (#is:invlist)
  (hyp concl:vprop)
  (extra:vprop { is_small extra })
  (f_elim:unit -> (
    stt_ghost unit (invlist_names is)
    (invlist_inv is ** extra ** hyp)
    (fun _ -> invlist_inv is ** concl)
  ))
: stt_ghost unit emp_inames extra (fun _ -> trade #is hyp concl)

val intro_trade_invs
  (#is:invlist)
  (hyp concl:vprop)
  (extra:vprop { is_small extra })
  (f_elim:unit -> (
    stt_ghost unit emp_inames
      (invlist_v is ** extra ** hyp)
      (fun _ -> invlist_v is ** concl)
  ))
: stt_ghost unit emp_inames extra (fun _ -> trade #is hyp concl)

val elim_trade
  (#is:invlist)
  (hyp concl:vprop)
: stt_ghost unit (invlist_names is)
    (invlist_inv is ** trade #is hyp concl ** hyp)
    (fun _ -> invlist_inv is ** concl)

val trade_sub_inv
  (#is1:invlist)
  (#is2:invlist { invlist_sub is1 is2 })
  (hyp concl:vprop)
: stt_ghost unit emp_inames
    (trade #is1 hyp concl)
    (fun _ -> trade #is2 hyp concl)

// Could weaken `f` to
// (f : unit -> stt_ghost unit (invlist_names os) (invlist_inv os ** q) (fun _ -> invlist_inv os ** r))
val trade_map
  (#os : invlist)
  (p q r : vprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
: stt_ghost unit emp_inames
    (trade #os p q)
    (fun _ -> trade #os p r)

val trade_compose
  (#os : invlist)
  (p q r : vprop)
: stt_ghost unit emp_inames
    (trade #os p q ** trade #os q r)
    (fun _ -> trade #os p r)
