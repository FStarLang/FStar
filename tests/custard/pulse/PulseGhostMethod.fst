(*
   Copyright 2008-2026 Microsoft Research

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

module PulseGhostMethod
(* Issue #4803: a method implemented by an [inline_for_extraction] fn whose
   body is all ghost steps.  The inlined lambda erases to a pure [()] and must
   still keep the unit thunk its arrow type keeps, both when bound to a local
   and when passed as an argument. *)
#lang-pulse
open Pulse.Lib.Pervasives

class ops = {
  res: nat -> slprop;
  step: x:UInt32.t -> n:Ghost.erased nat -> m:Ghost.erased nat ->
        stt unit (res n) (fun _ -> res m);
}

let my_res (n:nat) : slprop = emp

inline_for_extraction
fn ghostly_step (x:UInt32.t) (n:Ghost.erased nat) (m:Ghost.erased nat)
requires my_res n
ensures my_res m
{
  unfold (my_res n);
  fold (my_res m)
}

instance my_ops : ops = { res = my_res; step = ghostly_step }

(* The method passed on as a function value. *)
fn call_it (#r: nat -> slprop)
  (f: (x:UInt32.t -> n:Ghost.erased nat -> m:Ghost.erased nat ->
        stt unit (r n) (fun _ -> r m)))
  (x:UInt32.t) (n:Ghost.erased nat)
requires r n
ensures r 0
{
  f x n (Ghost.hide 0)
}

fn run_pass {| d:ops |} (x:UInt32.t) (n:Ghost.erased nat)
requires d.res n
ensures d.res 0
{
  call_it d.step x n
}

fn run {| d:ops |} (x:UInt32.t) (n:Ghost.erased nat)
requires d.res n
ensures d.res 0
{
  let s = d.step;
  s x n (Ghost.hide 0)
}

fn main ()
requires emp
ensures emp
{
  fold (my_res 1);
  rewrite (my_res 1) as (my_ops.res 1);
  run_pass #my_ops 0ul (Ghost.hide 1);
  run #my_ops 0ul (Ghost.hide 0);
  rewrite (my_ops.res 0) as (my_res 0);
  unfold (my_res 0)
}
