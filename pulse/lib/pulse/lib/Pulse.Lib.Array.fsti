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

module Pulse.Lib.Array
#lang-pulse
open Pulse.Lib.Core
include Pulse.Lib.Array.Core
open PulseCore.FractionalPermission
open FStar.Ghost
include Pulse.Lib.Array.Core
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
open Pulse.Class.PtsTo

fn compare
        (#t:eqtype)
        (l:SZ.t)
        (a1 a2:larray t (SZ.v l))
        (#p1 #p2:perm)
        (#s1 #s2:Ghost.erased (Seq.seq t))
  requires
     pts_to a1 #p1 s1 **
     pts_to a2 #p2 s2
  returns res : bool
  ensures
     pts_to a1 #p1 s1 **
     pts_to a2 #p2 s2 **
     pure (res <==> Seq.equal s1 s2)

fn memcpy_l
        (#t:eqtype)
        (l:SZ.t)
        (src dst:(a:array t { SZ.v l <= length a }))
        (#p:perm)
        (#src0 #dst0:Ghost.erased (Seq.seq t))
  requires pts_to src #p src0 **
           pts_to dst dst0
  returns  squash (Seq.length src0 == length src /\ Seq.length dst0 == length dst)
  ensures  pts_to src #p src0 **
           pts_to dst (Seq.append (Seq.slice src0 0 (SZ.v l))
                                   (Seq.slice dst0 (SZ.v l) (length dst)))

fn memcpy
        (#t:eqtype)
        (l:SZ.t)
        (src dst:larray t (SZ.v l))
        (#p:perm)
        (#src0 #dst0:Ghost.erased (Seq.seq t))
  requires
     pts_to src #p src0 **
     pts_to dst dst0
  ensures
     pts_to src #p src0 **
     pts_to dst src0

fn fill
        (#t:Type0)
        (l:SZ.t)
        (a:larray t (SZ.v l))
        (v:t)
        (#s:Ghost.erased (Seq.seq t))
  requires pts_to a s
  ensures
    exists* (s:Seq.seq t).
        pts_to a s **
        pure (s `Seq.equal` Seq.create (SZ.v l) v)

fn zeroize
        (l:SZ.t)
        (a:array U8.t{ SZ.v l == length a })
        (#s:Ghost.erased (Seq.seq U8.t))
  requires
   pts_to a s
  ensures
     exists* (s:Seq.seq U8.t).
       pts_to a s **
       pure (s `Seq.equal` Seq.create (SZ.v l) 0uy)
