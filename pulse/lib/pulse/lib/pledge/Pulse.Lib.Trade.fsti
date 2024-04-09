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

module Pulse.Lib.Trade

open Pulse.Lib.Core
open Pulse.Lib.InvList

module T = FStar.Tactics

val trade :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp:vprop) ->
  (concl:vprop) ->
  vprop

let ( ==>* ) :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp:vprop) ->
  (concl:vprop) ->
  vprop
  = fun #is -> trade #is

val intro_trade
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:vprop)
  (extra:vprop)
  (f_elim: unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    extra
    (fun _ -> trade #is hyp concl)

val intro_trade_invs
  (#[T.exact (`[])] is:invlist)
  (hyp concl extra:vprop)
  (f_elim: unit -> (
    stt_ghost unit emp_inames
    (invlist_v is ** extra ** hyp)
    (fun _ -> invlist_v is ** concl)
  ))
: stt_ghost unit emp_inames
    (invlist_inv is ** extra)
    (fun _ -> trade #(invlist_names is) hyp concl)

val elim_trade
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:vprop)
: stt_ghost unit is
    (trade #is hyp concl ** hyp)
    (fun _ -> concl)

val trade_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:vprop)
: stt_ghost unit emp_inames
    (trade #is1 hyp concl)
    (fun _ -> trade #is2 hyp concl)
