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

module Pulse.Lib.Forall

#lang-pulse
open Pulse.Lib.Core
open Pulse.Main
module T = FStar.Tactics.V2

[@@erasable]
let forall_f (#a:Type u#a) (p:a->slprop) (#[T.exact (`emp)] v:slprop) =
  x:a -> stt_ghost unit emp_inames v (fun _ -> p x)

val ( forall* )
    (#a:Type u#a)
    (p:a -> slprop)
: slprop

ghost
fn elim_forall u#a
  (#a : Type u#a)
  (#p : a->slprop)
  (x : a)
  requires forall* x. p x
  ensures  p x

ghost
fn intro_forall u#a
  (#a:Type u#a)
  (#p:a->slprop)
  (v:slprop)
  (f_elim : forall_f #a p #v)
  requires v
  ensures  forall* x. p x

val slprop_equiv_forall
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. p x == q x))
: slprop_equiv (op_forall_Star p) (op_forall_Star q)
