(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Fractional
#lang-pulse

open Pulse.Lib.Pervasives
open PulseCore.FractionalPermission

/// Helper lemma: half + half = whole
let half_plus_half (f : perm) : Lemma (f /. 2.0R +. f /. 2.0R == f) = ()

ghost
fn share_half (#p : perm -> slprop) {| d: fractional p |} (f : perm)
  requires p f
  ensures p (f /. 2.0R)
  ensures p (f /. 2.0R)
{
  half_plus_half f;
  rewrite (p f) as (p (f /. 2.0R +. f /. 2.0R));
  do_share #p #d (f /. 2.0R) (f /. 2.0R) ()
}

ghost
fn gather_half (#p : perm -> slprop) {| d: fractional p |} (f : perm)
  requires p (f /. 2.0R)
  requires p (f /. 2.0R)
  ensures p f
{
  do_gather #p #d (f /. 2.0R) (f /. 2.0R) ();
  half_plus_half f;
  rewrite (p (f /. 2.0R +. f /. 2.0R)) as (p f)
}
