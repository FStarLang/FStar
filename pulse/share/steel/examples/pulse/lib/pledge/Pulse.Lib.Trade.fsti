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
module T = FStar.Tactics

val trade :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop

let ( ==>* ) :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop
  = fun #is -> trade #is

val intro_trade
  (#[T.exact (`emp_inames)] is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: unit -> (
    stt_unobservable unit is
    (v ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    v
    (fun _ -> trade #is hyp concl)

val elim_trade
  (#[T.exact (`emp_inames)] is: inames)
  (hyp concl: vprop)
: stt_unobservable unit is
    ((trade #is hyp concl) ** hyp)
    (fun _ -> concl)

val trade_sub_inv
  (#os1 : inames)
  (#os2 : inames{inames_subset os1 os2})
  (hyp concl: vprop)
: stt_ghost unit emp_inames
    (trade #os1 hyp concl)
    (fun _ -> trade #os2 hyp concl)

// val ( forall* ) (#a:Type) (p:a->vprop) : vprop

// val intro_forall (#a:Type) (#p:a->vprop)
//     (v:vprop)
//     (f_elim : (x:a -> stt_unobservable unit emp_inames v (fun _ -> p x)))
// : stt_ghost unit emp_inames
//     v
//     (fun _ -> forall* x. p x)

// val elim_forall (#a:Type) (#p:a->vprop) (x:a)
// : stt_ghost unit emp_inames
//     (forall* x. p x)
//     (fun _ -> p x)
