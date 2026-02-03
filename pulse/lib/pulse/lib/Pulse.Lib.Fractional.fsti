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

///
/// Typeclass for Fractional Predicates
///
/// A fractional predicate `p : perm -> slprop` can be split and combined.
/// Instead of requiring definitional equality `p (f1 +. f2) == p f1 ** p f2`,
/// we provide ghost operations to convert between the two representations.
///

/// Type aliases for the share and gather operations
[@@erasable]
let share_t (p : perm -> slprop) (f1 f2 : perm) =
  stt_ghost unit emp_inames (p (f1 +. f2)) (fun _ -> p f1 ** p f2)

[@@erasable]
let gather_t (p : perm -> slprop) (f1 f2 : perm) =
  stt_ghost unit emp_inames (p f1 ** p f2) (fun _ -> p (f1 +. f2))

/// The fractional typeclass
[@@erasable]
class fractional (p : perm -> slprop) = {
  /// Split a combined permission into two separate permissions
  frac_share : (f1:perm) -> (f2:perm) -> unit -> share_t p f1 f2;
  
  /// Gather two separate permissions into a combined permission  
  frac_gather : (f1:perm) -> (f2:perm) -> unit -> gather_t p f1 f2;
}

/// Wrapper to call share
let do_share (#p : perm -> slprop) {| d : fractional p |} (f1 f2 : perm) ()
  : stt_ghost unit emp_inames (p (f1 +. f2)) (fun _ -> p f1 ** p f2) = d.frac_share f1 f2 ()

/// Wrapper to call gather  
let do_gather (#p : perm -> slprop) {| d : fractional p |} (f1 f2 : perm) ()
  : stt_ghost unit emp_inames (p f1 ** p f2) (fun _ -> p (f1 +. f2)) = d.frac_gather f1 f2 ()

/// Convenience: share into halves
ghost
fn share_half (#p : perm -> slprop) {| fractional p |} (f : perm)
  requires p f
  ensures p (f /. 2.0R) ** p (f /. 2.0R)

/// Convenience: gather from halves
ghost
fn gather_half (#p : perm -> slprop) {| fractional p |} (f : perm)
  requires p (f /. 2.0R) ** p (f /. 2.0R)
  ensures p f
