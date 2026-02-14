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
module MS = Pulse.Lib.PCM.MonoidShares
module GPR = Pulse.Lib.GhostPCMReference

let pcm_of (n:nat) = MS.pcm_of MS.nat_plus_cm n

let tank (n:nat) = GPR.gref (pcm_of n)

inline_for_extraction
instance non_informative_tank (n:nat)
  : Pulse.Lib.NonInformative.non_informative (tank n)
  = { reveal = ((fun x -> x) <: Pulse.Lib.NonInformative.revealer (tank n)) }

let owns #n ([@@@mkey] g : tank n) (i:nat)
: timeless_slprop
= GPR.pts_to #_ #(pcm_of n) g i

instance owns_placeless #n g i = Tactics.Typeclasses.solve

ghost
fn alloc (n:nat)
  returns g : tank n
  ensures  owns g n
{
  let g = GPR.alloc #_ #(pcm_of n) n;
  fold (owns g n);
  g
}

ghost
fn extract_bound (#n:nat) (g:tank n) (#i:erased nat)
requires
  owns g i
ensures
  owns g i ** pure (i <= n)
{
  unfold owns;
  let v = GPR.read_simple g; 
  fold owns;
}

[@@allow_ambiguous]
ghost
fn gather (#n:nat) (g:tank n) (#i #j:erased nat)
requires
  owns g i **
  owns g j
ensures
  owns g (i + j) **
  pure (i <= n /\ j <= n /\ i + j <= n)
{
  extract_bound g #i;
  extract_bound g #j;
  unfold (owns g i);
  unfold (owns g j);
  GPR.gather g _ _;
  fold owns;
  extract_bound g;
}

ghost
fn share (#n:nat) (g:tank n) (#u #v:nat)
requires
  owns g (u + v)
ensures
  owns g u **
  owns g v
{
  open FStar.PCM;
  unfold owns;
  rewrite (GPR.pts_to g (u + v))
       as (GPR.pts_to g (op (pcm_of n) u v));
  GPR.share g u v;
  fold (owns g u);
  fold (owns g v)
}

ghost
fn share_one (#n:nat) (g:tank n) (#u:nat { u > 0 })
requires
  owns g u
returns k:erased nat
ensures
  owns g (u - 1) **
  owns g 1 **
  pure (k == u - 1)
{
  open FStar.PCM;
  unfold owns;
  rewrite (GPR.pts_to g u)
       as (GPR.pts_to g (op (pcm_of n) (u - 1) 1));
  GPR.share g (u-1) 1;
  fold (owns g (u - 1));
  fold (owns g 1);
  (hide #nat (u - 1))
}
