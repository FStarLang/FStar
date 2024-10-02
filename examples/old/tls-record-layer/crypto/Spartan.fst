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
module Spartan

open FStar.HyperStack.ST
open FStar.Buffer

type u8=FStar.UInt8.t

assume val keyExpansion:
  key:buffer u8 ->
  w:buffer u8 ->
  sb:buffer u8 -> Stack unit
  (requires (fun h -> live h key /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> modifies_1 w h0 h1))

assume val cipher:
  out:buffer u8 ->
  input:buffer u8 ->
  w:buffer u8 ->
  sb:buffer u8 -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> modifies_1 out h0 h1))
