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

module ExistsSyntax
#lang-pulse
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference


fn some_function (r0:ref U8.t) (r1:ref U8.t) (#s:erased U8.t)
   requires 
      R.pts_to r0 s **
      (exists* (s1:U8.t). R.pts_to r1 s1)
   ensures
        emp
{
    let x = !r0;
    let y = !r1;
    admit()
}




fn call_some_function (r0:ref U8.t) (r1:ref U8.t) (#s0:erased U8.t) (#s1:erased U8.t)
   requires
     R.pts_to r0 s0 **
     R.pts_to r1 s1
   ensures
     emp
{
    some_function r0 r1;
    ()
}

