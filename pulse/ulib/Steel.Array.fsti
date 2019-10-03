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
module Steel.Array

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = LowStar.ModifiesGen

open Steel.RST

include Steel.Array.Views

val index (#a:Type) (b:A.array a) (i:UInt32.t)
  : RST a (array_resource b)
    (fun _ -> array_resource b)
    (fun _ -> UInt32.v i < A.vlength b)
    (fun h0 x h1 ->
      UInt32.v i < A.vlength b /\
      Seq.index (as_rseq b h0) (UInt32.v i) == x /\
      h0 == h1
    )

val upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a)
  : RST unit (array_resource b)
    (fun _ -> array_resource b)
    (fun h0 -> UInt32.v i < A.vlength b /\ P.allows_write (get_rperm b h0))
    (fun h0 _ h1 -> UInt32.v i < A.vlength b /\
      as_rseq b h1 ==
      Seq.upd (as_rseq b h0) (UInt32.v i) v /\
      get_rperm b h1 == get_rperm b h0
    )

val alloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (A.array a)
    (empty_resource)
    (fun b -> array_resource b)
    (fun _ -> UInt32.v len > 0)
    (fun _ b h1 ->
      A.freeable b /\
      as_rseq b h1 == Seq.create (UInt32.v len) init /\
      get_rperm b h1 == P.full_permission /\
      A.vlength b = UInt32.v len
    )

val free (#a:Type) (b:A.array a)
  : RST unit (array_resource b)
    (fun _ -> empty_resource)
    (fun h0 -> A.freeable b /\ P.allows_write (get_rperm b h0))
    (fun _ _ _ -> True)

val share (#a:Type) (b:A.array a)
  : RST (A.array a)
        (array_resource b)
        (fun b' -> array_resource b <*> array_resource b')
        (fun _ -> A.vlength b > 0)
        (fun h0 b' h1 ->
          A.vlength b' = A.vlength b /\
          as_rseq b h0 == as_rseq b h1 /\
          as_rseq b' h1 == as_rseq b h1 /\
          get_rperm b h1 == P.half_permission (get_rperm b h0) /\
          get_rperm b' h1  == P.half_permission (get_rperm b h0) /\
          summable_permissions b b' h1
        )

val gather (#a:Type) (b b':A.array a)
  : RST unit (array_resource b <*> array_resource b')
    (fun _ -> array_resource b)
    (fun h0 -> A.gatherable b b' /\ summable_permissions b b' h0)
    (fun h0 _ h1 ->
      summable_permissions b b' h0 /\
      as_rseq b h0 == as_rseq b h1 /\
      get_rperm b h1 == P.sum_permissions (get_rperm b h0) (get_rperm b' h0)
    )


val split (#a: Type) (b: A.array a) (idx: UInt32.t)
  : RST (A.array a & A.array a)
    (array_resource b)
    (fun p -> array_resource (fst p) <*> array_resource (snd p))
    (fun _ -> UInt32.v idx > 0 /\ UInt32.v idx < A.vlength b)
    (fun h0 bs h1 ->
      UInt32.v idx > 0 /\ UInt32.v idx < A.vlength b /\
      A.is_split_into b (fst bs, snd bs) /\
      as_rseq (fst bs) h1 == Seq.slice (as_rseq b h0) 0 (UInt32.v idx) /\
      as_rseq (snd bs) h1 == Seq.slice (as_rseq b h0) (UInt32.v idx) (A.vlength b) /\
      A.vlength (fst bs) = UInt32.v idx /\
      A.vlength (snd bs) = A.vlength b - UInt32.v idx /\
      get_rperm (fst bs) h1 == get_rperm b h0 /\
      get_rperm (snd bs) h1 == get_rperm b h0
    )

val glue (#a: Type) (b b1 b2: A.array a)
  : RST unit
    (array_resource b1 <*> array_resource b2)
    (fun _ -> array_resource b)
    (fun h0 -> A.is_split_into b (b1, b2) /\ get_rperm b1 h0 == get_rperm b2 h0)
    (fun h0 _ h1 ->
      as_rseq b h1 == Seq.append (as_rseq b1 h0) (as_rseq b2 h0) /\
      get_rperm b h1 == get_rperm b1 h0
    )

val copy (#a: Type) (o: array a) (i: array a) : RST unit
  (array_resource o <*> array_resource i)
  (fun _ -> array_resource o <*> array_resource i)
  (fun h ->
    A.vlength o = A.vlength i /\
    P.allows_write (get_rperm o h)
  )
  (fun h0 _ h1 ->
    A.vlength o = A.vlength i /\
    focus_rmem h0 (array_resource i) == focus_rmem h1 (array_resource i) /\
    as_rseq o h1 == as_rseq i h0 /\
    get_rperm o h1 == get_rperm o h0
  )
