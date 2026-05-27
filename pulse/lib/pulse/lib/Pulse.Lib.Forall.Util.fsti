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

module Pulse.Lib.Forall.Util
#lang-pulse
open Pulse.Lib.Pervasives
include Pulse.Lib.Forall
module T = FStar.Tactics.V2
open Pulse.Lib.Trade { ( @==> ) }

(* Aliases for clients *)
let elim #a #p = Pulse.Lib.Forall.elim_forall #a #p

ghost
fn trans_compose (#a #b #c:Type0) (p:a -> slprop) (q:b -> slprop) (r:c -> slprop)
                 (f: a -> GTot b) (g: b -> GTot c)
    requires (forall* x. p x @==> q (f x))
    requires (forall* x. q x @==> r (g x))
    ensures forall* x. p x @==> r (g (f x))

ghost
fn trans (#a:Type0) (p q r: a -> slprop)
    requires (forall* x. p x @==> q x)
    requires (forall* x. q x @==> r x)
    ensures forall* x. p x @==> r x

ghost fn elim_forall_imp (#a:Type0) (p q: a -> slprop) (x:a)
    requires (forall* x. p x @==> q x)
    requires p x
    ensures q x

[@@erasable]
let forall_imp_f #a (p: a -> slprop) (#[T.exact (`emp)] r: slprop) (q: a -> slprop) =
    u:a -> stt_ghost unit emp_inames (r ** p u) (fun _ -> q u)

ghost
fn intro_forall_imp (#a:Type0) (p q: a -> slprop) (r:slprop)
    (elim: forall_imp_f p #r q)
  requires r
  ensures forall* x. p x @==> q x
