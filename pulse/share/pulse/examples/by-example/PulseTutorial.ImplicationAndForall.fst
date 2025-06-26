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

module PulseTutorial.ImplicationAndForall
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
open Pulse.Lib.Forall.Util
module I = Pulse.Lib.Trade.Util
module GR = Pulse.Lib.GhostReference
open GR

//regain_half$
let regain_half #a (x:GR.ref a) (v:a) =
  pts_to x #0.5R v @==> pts_to x v
//end regain_half$


//intro_regain_half$
ghost 
fn intro_regain_half (x:GR.ref int)
requires pts_to x 'v
ensures pts_to x #0.5R 'v ** regain_half x 'v
{
  ghost
  fn aux ()
  requires pts_to x #0.5R 'v ** pts_to x #0.5R 'v
  ensures pts_to x 'v
  {
    GR.gather x;
  };
  GR.share x;
  I.intro _ _ _ aux;
  fold regain_half;
}
//end intro_regain_half$

//use_regain_half$
ghost
fn use_regain_half (x:GR.ref int)
requires pts_to x #0.5R 'v ** regain_half x 'v
ensures pts_to x 'v
{
  unfold regain_half;
  I.elim _ _;
}
//end use_regain_half$


//regain_half_q$
let regain_half_q #a (x:GR.ref a) =
  forall* u. pts_to x #0.5R u @==> pts_to x u 
//end regain_half_q$


module FA = Pulse.Lib.Forall.Util

//intro_regain_half_q$
ghost 
fn intro_regain_half_q (x:GR.ref int)
requires pts_to x 'v
ensures pts_to x #0.5R 'v ** regain_half_q x
{
  ghost
  fn aux1 (u:int)
  requires pts_to x #0.5R 'v ** pts_to x #0.5R u
  ensures pts_to x u
  {
    gather x;
  };
  GR.share x;
  FA.intro_forall_imp _ _ _ aux1;
  fold regain_half_q;
}
//end intro_regain_half_q$

//use_regain_half_q$
ghost
fn use_regain_half_q (x:GR.ref int)
requires pts_to x #0.5R 'u ** regain_half_q x
ensures pts_to x 'u
{
  unfold regain_half_q;
  FA.elim #_ #(fun u -> pts_to x #0.5R u @==> pts_to x u) 'u;
  I.elim _ _;
}
//end use_regain_half_q$


//can_update$
let can_update (x:GR.ref int) = 
  forall* u v. pts_to x #0.5R u @==>
               pts_to x v
//end can_update$

//make_can_update$
ghost
fn make_can_update (x:GR.ref int)
requires pts_to x 'w
ensures pts_to x #0.5R 'w ** can_update x
{
  ghost
  fn aux (u:int)
  requires pts_to x #0.5R 'w
  ensures forall* v. pts_to x #0.5R u @==> pts_to x v
  {
    ghost
    fn aux (v:int)
    requires pts_to x #0.5R 'w ** pts_to x #0.5R u
    ensures pts_to x v
    {
      gather x;
      x := v;
    };
    FA.intro_forall_imp _ _ _ aux;
  };
  share x;
  FA.intro _ aux;
  fold (can_update x);
}
//end make_can_update$


//update$
ghost
fn update (x:GR.ref int) (k:int)
requires pts_to x #0.5R 'u ** can_update x
ensures pts_to x #0.5R k ** can_update x
{
  unfold can_update;
  FA.elim #_ #(fun u -> forall* v. pts_to x #0.5R u @==> pts_to x v) 'u;
  FA.elim #_ #(fun v -> pts_to x #0.5R 'u @==> pts_to x v) k;
  I.elim _ _;
  make_can_update x;
}
//end update$