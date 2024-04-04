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
open Pulse.Lib.Pervasives
open Pulse.Lib.InvList
module T = FStar.Tactics

val trade :
  (#[T.exact (`invlist_empty)] is : invlist) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop

let ( ==>* ) :
  (#[T.exact (`invlist_empty)] is : invlist) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop
  = fun #is -> trade #is

val intro_trade
  (#[T.exact (`invlist_empty)] is : invlist)
  (hyp concl: vprop)
  (extra: vprop)
  (f_elim: unit -> (
    stt_ghost unit emp_inames
    (invlist_v is ** extra ** hyp)
    (fun _ -> invlist_v is ** concl)
  ))
: stt_ghost unit emp_inames
    extra
    (fun _ -> trade #is hyp concl)

val elim_trade
  (#[T.exact (`invlist_empty)] is : invlist)
  (hyp concl: vprop)
: stt_ghost unit (invlist_names is)
    (invlist_inv is ** (trade #is hyp concl) ** hyp)
    (fun _ -> invlist_inv is ** concl)

val trade_sub_inv
  (#os1 : invlist)
  (#os2 : invlist{invlist_sub os1 os2})
  (hyp concl: vprop)
: stt_ghost unit (invlist_names os1)
    (invlist_inv os1 ** trade #os1 hyp concl)
    (fun _ -> invlist_inv os1 ** trade #os2 hyp concl)
