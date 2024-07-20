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

module PulseLambdas
#lang-pulse
open Pulse.Lib.Pervasives

let stt_trivial a = stt a emp (fun _ -> emp)

(*
fn test_trivial_function (x:int)
: stt_trivial int
= { //should allow nullary "lambdas"
    (x + 1)
  }
*)

let swap_fun = #a:Type0 -> x:ref a -> y:ref a -> #vx:erased a -> #vy:erased a -> stt unit
    (requires pts_to x vx ** pts_to y vy)
    (ensures fun _ -> pts_to x vy ** pts_to y vx)



fn s1 () 
  : swap_fun 
  = (#a:Type0) (x y #_vx #_vy:_)
    {
      let vx = !x;
      let vy = !y;
      x := vy;
      y := vx;
    }


let ss = s1

[@@expect_failure]

fn s2 ()
  : swap_fun 
  = (#a:Type0) (x y:_) //make it so that implicit binders in the type can be left out
    {
      let vx = !x;
      let vy = !y;
      x := vy;
      y := vx;
    }

(*
fn s3 () : swap_fun
  = (#a:Type0) (x y #_vx #_vy:_)
    requires pts_to x _vx ** pts_to y _vy //reject repeated annotation
    ensures  pts_to x _vy ** pts_to y _vx
    {
      let vx = !x;
      let vy = !y;
      x := vy;
      y := vx;
    }
    {
      let vx = !x;
      let vy = !y;
      x := vy;
      y := vx;
    }
*)


fn test_inner_lambda (#a:Type0)
                     (x y:ref int)
requires pts_to x 'vx ** pts_to y 'vy
ensures  pts_to x 'vy ** pts_to y 'vy
{
  fn write_helper (#a:Type) (x:ref a) (n:a) (#vx:erased a)
    requires pts_to x vx
    ensures  pts_to x n
  {
    x := n;
  };
  let vx = !x;
  let vy = !y;
  write_helper x vy;
  write_helper y vy;
} 

