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

module Pulse.Lib.ConditionVar
#lang-pulse
open Pulse.Lib.Pervasives

val cvar_t : Type0

val inv_name (c:cvar_t) : iname

val send (c:cvar_t) (p:slprop) : slprop

val recv (c:cvar_t) (p:slprop) : slprop

instance val is_send_send c p : is_send (send c p)
instance val is_send_recv c p : is_send (recv c p)

fn create (p:slprop) {| is_send p |}
  requires emp
  returns c:cvar_t
  ensures send c p ** recv c p

atomic
fn signal_atomic (c:cvar_t) (#p:slprop)
  requires send c p
  requires p
  requires later_credit 1
  ensures emp
  opens [ inv_name c ]

fn signal (c:cvar_t) (#p:slprop)
  requires send c p
  requires p
  ensures emp

fn wait (b:cvar_t) (#p:slprop)
  requires recv b p
  ensures p

ghost
fn split (b:cvar_t) (#p #q:slprop) {| is_send p, is_send q |}
  requires recv b (p ** q)
  requires later_credit 2
  ensures recv b p ** recv b q
  opens [ inv_name b ]
