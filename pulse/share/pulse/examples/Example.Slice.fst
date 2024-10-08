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
module Example.Slice
#lang-pulse
open Pulse
open Pulse.Lib.Slice

fn test () requires emp ensures emp {
  let arr = Pulse.Lib.Array.alloc 42uy 10sz;
  let slice = from_array arr 10sz;
  let SlicePair s1 s2 = split slice 2sz;
  share s2;
  let x = s2.(2sz);
  s1.(1sz) <- x;
  gather s2;
  join s1 s2 slice;
  to_array slice;
  Pulse.Lib.Array.free arr;
}