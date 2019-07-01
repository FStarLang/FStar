(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.RST.Array

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = FStar.ModifiesGen

open LowStar.Resource
open LowStar.RST

include LowStar.RST.Array.Views

val index (#a:Type) (b:A.array a) (i:UInt32.t)
  : RST a (array_resource b)
          (fun _ -> array_resource b)
          (fun h0 -> UInt32.v i < A.vlength b)
          (fun h0 x h1 ->
          UInt32.v i < A.vlength b /\
          Seq.index (sel (array_view b) h0).s (UInt32.v i) == x /\
          sel (array_view b) h0 == sel (array_view b) h1
          )

val upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a)
  : RST unit (array_resource b)
             (fun _ -> array_resource b)
             (fun h0 -> UInt32.v i < A.vlength b /\ P.allows_write (sel (array_view b) h0).p )
             (fun h0 _ h1 -> UInt32.v i < A.vlength b /\
             (sel (array_view b) h1).s ==
             Seq.upd (sel (array_view b) h0).s (UInt32.v i) v /\
             (sel (array_view b) h1).p == (sel (array_view b) h0).p
             )

val alloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (A.array a)
        (empty_resource)
        (fun b -> array_resource b)
        (fun _ -> UInt32.v len > 0)
        (fun _ b h1 ->
        A.freeable b /\
        (sel (array_view b) h1).s == Seq.create (UInt32.v len) init /\
        (sel (array_view b) h1).p = FStar.Real.one
        )

val free (#a:Type) (b:A.array a)
  : RST unit (array_resource b)
             (fun _ -> empty_resource)
             (fun h0 -> A.freeable b /\ P.allows_write (sel (array_view b) h0).p)
             (fun _ _ _ -> True)

val share (#a:Type) (b:A.array a)
  : RST (A.array a)
        (array_resource b)
        (fun b' -> array_resource b <*> array_resource b')
        (fun h0 -> A.vlength b > 0)
        (fun h0 b' h1 ->
          (sel (array_view b) h0).s == (sel (array_view b) h1).s /\
          (sel (array_view b') h1).s == (sel (array_view b) h1).s /\
          (sel (array_view b) h1).p == P.half_permission (sel (array_view b) h0).p /\
          (sel (array_view b') h1).p == P.half_permission (sel (array_view b) h0).p /\
          summable_permissions h1 b b')

val merge (#a:Type) (b b':A.array a)
  : RST unit (array_resource b <*> array_resource b')
             (fun _ -> array_resource b)
             (fun h0 -> A.mergeable b b' /\ summable_permissions h0 b b')
             (fun h0 _ h1 ->
               summable_permissions h0 b b' /\
               (sel (array_view b) h0).s == (sel (array_view b) h1).s /\
               (sel (array_view b) h1).p == P.sum_permissions (sel (array_view b) h0).p (sel (array_view b') h0).p)
    
