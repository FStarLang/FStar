(*
   Copyright 2008-2018 Microsoft Research

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
module MemCpy
open Pulse
#lang-pulse
open Pulse.Lib.Array
module V = Pulse.Lib.Vec
module U8 = FStar.UInt8
module SZ = FStar.SizeT

fn memcpy_vec
    (len:SZ.t)
    (src dest:V.vec U8.t)
    (#f:perm)
preserves
  src |-> Frac f 's
requires 
  pure (
    V.length src == SZ.v len /\
    V.length src == V.length dest
  )
requires
  exists* s. dest |-> s
ensures
  dest |-> 's
{ 
  V.to_array_pts_to dest;
  V.to_array_pts_to src ;
  Pulse.Lib.Array.memcpy len (V.vec_to_array src) (V.vec_to_array dest);
  V.to_vec_pts_to dest;
  V.to_vec_pts_to src;
}

//SNIPPET_START: malloc_copy_free
fn malloc_copy_free (v:V.vec U8.t) (len:SZ.t)
requires v |-> 's
requires pure (V.length v == SZ.v len /\ V.is_full_vec v)
returns u:V.vec U8.t
ensures u |-> 's

{
  let u = V.alloc 0uy len;
  memcpy_vec len v u;
  V.free v;
  u
}
//SNIPPET_END: malloc_copy_free
