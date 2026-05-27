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
module Pulse.Lib.Tank
#lang-pulse
open Pulse.Lib.Pervasives

// A tank is a ghost resource with a fixed capacity `n`
[@@erasable]
val tank (n:nat) : Type0

inline_for_extraction
instance val non_informative_tank (n:nat)
  : Pulse.Lib.NonInformative.non_informative (tank n)

// A predicate asserting ownership of `i` units of the tank
val owns (#n:nat) ([@@@mkey] g : tank n) (i:nat) : timeless_slprop

instance val owns_placeless (#n:nat) (g : tank n) (i:nat) : placeless (owns g i)

// Allocate a new tank of capacity `n`, returning ownership of all `n` units
ghost
fn alloc (n:nat)
  returns g : tank n
  ensures  owns g n

// You cannot own more than the tank capacity
ghost
fn extract_bound (#n:nat) (g:tank n) (#i:erased nat)
  requires owns g i
  ensures  owns g i ** pure (i <= n)

// Ownership of tank units can be combined additively
[@@allow_ambiguous]
ghost
fn gather (#n:nat) (g:tank n) (#i #j:erased nat)
  requires owns g i ** owns g j
  ensures  owns g (i + j) ** pure (i <= n /\ j <= n /\ i + j <= n)

// Ownership can be split
ghost
fn share (#n:nat) (g:tank n) (#u #v:nat)
  requires owns g (u + v)
  ensures  owns g u ** owns g v

// Split off exactly one unit
ghost
fn share_one (#n:nat) (g:tank n) (#u:nat { u > 0 })
  requires owns g u
  returns  k:erased nat
  ensures  owns g (u - 1) ** owns g 1 ** pure (k == u - 1)
