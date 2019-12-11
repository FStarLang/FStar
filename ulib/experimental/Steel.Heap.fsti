(*
   Copyright 2019 Microsoft Research

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
module Steel.Heap
module U32 = FStar.UInt32

/// Abstract type of memories
val heap  : Type u#1

/// A memory maps a reference to its associated value
val ref (a:Type u#0) : Type u#0
val array_ref (a: Type u#0) : Type u#0

val offset (#t: Type) (a: array_ref t) : GTot (n:U32.t{U32.v n >= 0})
val length (#t: Type) (a: array_ref t) : GTot (n:U32.t{U32.v n >= 0})

/// A predicate describing non-overlapping memories
val disjoint (m0 m1:heap) : prop

/// disjointness is symmetric
val disjoint_sym (m0 m1:heap)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)

/// disjoint memories can be combined
val join (m0:heap) (m1:heap{disjoint m0 m1}) : heap

/// disjointness distributes over join
val disjoint_join (m0 m1 m2:heap)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)

val join_commutative (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint_sym m0 m1;
       join m0 m1 == join m1 m0))

val join_associative (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) == join (join m0 m1) m2))
