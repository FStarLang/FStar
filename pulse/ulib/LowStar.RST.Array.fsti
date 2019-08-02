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
    (fun _ -> UInt32.v i < A.vlength b)
    (fun old x modern ->
      UInt32.v i < A.vlength b /\
      Seq.index (as_seq b old) (UInt32.v i) == x /\
      old == modern
    )

val upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a)
  : RST unit (array_resource b)
    (fun _ -> array_resource b)
    (fun old -> UInt32.v i < A.vlength b /\ P.allows_write (get_perm b old))
    (fun old _ modern -> UInt32.v i < A.vlength b /\
      as_seq b modern ==
      Seq.upd (as_seq b old) (UInt32.v i) v /\
      get_perm b modern == get_perm b old
    )

val alloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (A.array a)
    (empty_resource)
    (fun b -> array_resource b)
    (fun _ -> UInt32.v len > 0)
    (fun _ b modern ->
      A.freeable b /\
      as_seq b modern == Seq.create (UInt32.v len) init /\
      get_perm b modern = FStar.Real.one
    )

val free (#a:Type) (b:A.array a)
  : RST unit (array_resource b)
    (fun _ -> empty_resource)
    (fun old -> A.freeable b /\ P.allows_write (get_perm b old))
    (fun _ _ _ -> True)

val share (#a:Type) (b:A.array a)
  : RST (A.array a)
        (array_resource b)
        (fun b' -> array_resource b <*> array_resource b')
        (fun _ -> A.vlength b > 0)
        (fun old b' modern ->
          A.vlength b' = A.vlength b /\
          as_seq b old == as_seq b modern /\
          as_seq b' modern == as_seq b modern /\
          get_perm b modern == P.half_permission (get_perm b old) /\
          get_perm b' modern  == P.half_permission (get_perm b old) /\
          summable_permissions b b' modern
        )

val gather (#a:Type) (b b':A.array a)
  : RST unit (array_resource b <*> array_resource b')
    (fun _ -> array_resource b)
    (fun old -> A.gatherable b b' /\ summable_permissions b b' old)
    (fun old _ modern ->
      summable_permissions b b' old /\
      as_seq b old == as_seq b modern /\
      get_perm b modern == P.sum_permissions (get_perm b old) (get_perm b' old)
    )


val split (#a: Type) (b: A.array a) (idx: UInt32.t{UInt32.v idx > 0 /\ UInt32.v idx < A.vlength b})
  : RST (A.array a & A.array a)
    (array_resource b)
    (fun p -> array_resource (fst p) <*> array_resource (snd p))
    (fun _ -> True)
    (fun old bs modern ->
      A.is_split_into b (fst bs, snd bs) /\
      as_seq (fst bs) modern == Seq.slice (as_seq b old) 0 (UInt32.v idx) /\
      as_seq (snd bs) modern == Seq.slice (as_seq b old) (UInt32.v idx) (A.vlength b) /\
      get_perm (fst bs) modern == get_perm b old /\
      get_perm (snd bs) modern == get_perm b old
    )

val glue (#a: Type) (b b1 b2: A.array a)
  : RST unit
    (array_resource b1 <*> array_resource b2)
    (fun _ -> array_resource b)
    (fun old -> A.is_split_into b (b1, b2) /\ get_perm b1 old == get_perm b2 old)
    (fun old _ modern ->
      as_seq b modern == Seq.append (as_seq b1 old) (as_seq b2 old) /\
      get_perm b modern == get_perm b1 old
    )
