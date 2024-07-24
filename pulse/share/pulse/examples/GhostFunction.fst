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

module GhostFunction
#lang-pulse
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference

assume val f (x:int) : GTot int

//
// calling GTot functions in ghost functions is ok
//

ghost
fn test_gtot (x:GR.ref int)
  requires GR.pts_to x 0
  ensures GR.pts_to x (f 0)
{
  open GR;
  let y = f 0;
  x := y
}



fn increment (x:GR.ref int) (#n:erased int)
    requires GR.pts_to x n
    ensures GR.pts_to x (n + 1)
{  
   open GR;
   let v = !x;
   x := (v + 1);
}



ghost
fn incrementg (x:GR.ref int) (#n:erased int)
    requires GR.pts_to x n
    ensures GR.pts_to x (n + 1)
{
   open GR;
   let v = !x;
   x := (v + 1)
}



ghost
fn test_gtot_app_f (x:GR.ref int) (y:int)
  requires GR.pts_to x 0
  ensures GR.pts_to x y
{
  open GR;
  x := y
}


//
// ghost arguments to STGhost functions are ok
//

ghost
fn test_gtot_app (x:GR.ref int)
  requires GR.pts_to x 0
  ensures GR.pts_to x (f 0)
{
  test_gtot_app_f x (f 0)
}

