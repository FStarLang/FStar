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

module PulseTutorial.Intro
#lang-pulse
open Pulse.Lib.Pervasives




fn par (#p #q #r #s:_)
       (f: (unit -> stt unit p (fun _ -> q)))
       (g: (unit -> stt unit r (fun _ -> s)))
requires p ** r
ensures q ** s
{
    parallel
    requires p and r
    ensures  q and s
        { f () }
        { g () };
    ()
}


let incr_functional (x:int) = x + 1

//incr$
fn incr (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 1)
{
    let v = !x;
    x := v + 1;
}
//end incr$

//incr_explicit_i$
fn incr_explicit_i (x:ref int) (i:erased int)
requires pts_to x i
ensures pts_to x (i + 1)
{
    let v = !x;
    x := v + 1;
}
//end incr_explicit_i$

//par_incr$
fn par_incr (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y ('j + 1)
{
   par (fun _ -> incr x)
       (fun _ -> incr y)
}
//end par_incr$


//incr_frame$
fn incr_frame (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y 'j
{
   incr x;
}
//end incr_frame$

//incr_frame_any$
fn incr_frame_any (x:ref int) (f:slprop)
requires pts_to x 'i ** f
ensures pts_to x ('i + 1) ** f
{
   incr x;
}
//end incr_frame_any$