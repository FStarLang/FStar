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

module T = FStar.Tactics

val trade :
  (#[T.exact (`[])] is:inames) ->
  (hyp:slprop) ->
  (concl:slprop) ->
  slprop

val trade_is_timeless (#is:inames) (hyp concl:slprop)
  : Lemma (timeless (trade #is hyp concl))

val intro_trade
  (#is:inames)
  (hyp concl:slprop)
  (extra:slprop { timeless extra })
  (f_elim:unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames extra (fun _ -> trade #is hyp concl)

val elim_trade
  (#is:inames)
  (hyp concl:slprop)
: stt_ghost unit is
    (trade #is hyp concl ** hyp)
    (fun _ -> concl)

val trade_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
: stt_ghost unit emp_inames
    (trade #is1 hyp concl)
    (fun _ -> trade #is2 hyp concl)

// Could weaken `f` to
// (f : unit -> stt_ghost unit (invlist_names os) (invlist_inv os ** q) (fun _ -> invlist_inv os ** r))
val trade_map
  (#os : inames)
  (p q r : slprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
: stt_ghost unit emp_inames
    (trade #os p q)
    (fun _ -> trade #os p r)

val trade_compose
  (#os : inames)
  (p q r : slprop)
: stt_ghost unit emp_inames
    (trade #os p q ** trade #os q r)
    (fun _ -> trade #os p r)
