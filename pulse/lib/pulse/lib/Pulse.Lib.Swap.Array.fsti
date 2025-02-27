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

module Pulse.Lib.Swap.Array
#lang-pulse
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array

noextract [@@noextract_to "krml"]
let array_swap_post
  (lb: SZ.t) (rb: SZ.t)
  (mb: SZ.t)
  (mb': SZ.t)
: Tot prop
=
      SZ.v lb <= SZ.v mb /\
      SZ.v mb <= SZ.v rb /\
      SZ.v mb' == SZ.v lb + (SZ.v rb - SZ.v mb)

inline_for_extraction noextract [@@noextract_to "krml"]
val array_swap
  (#t: Type0)
  (a: A.array t)
  (lb: SZ.t) (rb: SZ.t)
  (mb: SZ.t)
  (#s1 #s2: Ghost.erased (Seq.seq t))
: stt SZ.t
  (
    A.pts_to_range a (SZ.v lb) (SZ.v mb) s1 **
    A.pts_to_range a (SZ.v mb) (SZ.v rb) s2
  )
  (fun mb' ->
    A.pts_to_range a (SZ.v lb) (SZ.v mb') s2 **
    A.pts_to_range a (SZ.v mb') (SZ.v rb) s1 **
    pure (array_swap_post lb rb mb mb')
  )
