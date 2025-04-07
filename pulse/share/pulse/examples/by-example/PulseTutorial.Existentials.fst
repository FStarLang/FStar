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

module PulseTutorial.Existentials
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Mul

//assign$
fn assign #a (x:ref a) (v:a)
requires
  exists* w. pts_to x w
ensures
  pts_to x v
{
  x := v
}
//end assign$

//incr_fail$
[@@expect_failure] 
fn incr #a (x:ref int)
requires
  exists* w0. pts_to x w
ensures 
  pts_to x (w0 + 1) //w0 is not in scope here
{
  let w = !x
  x := w + 1
}
//end incr_fail$

//make_even$
fn make_even (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  let v = !x;
  x := v + v;
}
//end make_even$


//make_even_explicit$
fn make_even_explicit (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  with w0. assert (pts_to x w0);
  let v = !x; // v:int; _:squash(v==w0); Ctxt=pts_to x v
  x := v + v; //                          ... pts_to x (v + v)
  introduce
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
  with (v + v);
}
//end make_even_explicit$


//make_even_explicit_alt$
fn make_even_explicit_alt (x y:ref int)
requires
  exists* wx wy. pts_to x wx ** pts_to y wy ** pure (wx % 2 == wy % 2)
ensures
  exists* wx' wy'. pts_to x wx' ** pts_to y wy' ** pure (wx' % 2 == 0)
{
  with wx wy. _;
  let vx = !x; 
  let vy = !y;
  x := vx + vy;
  introduce exists* wx' wy'. pts_to x wx' ** pts_to y wy' ** pure (wx' % 2 == 0)
  with (vx + vy) vy;
}
//end make_even_explicit_alt$


//call_make_even$
fn call_make_even (x:ref int)
requires
  pts_to x 'v
ensures
  exists* w. pts_to x w ** pure (w % 2 == 0)
{
  make_even x;
}
//end call_make_even$