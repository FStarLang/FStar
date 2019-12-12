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
module Steel.Memory
open Steel.Heap
open Steel.HProp
open FStar.Real
open Steel.Permissions
module U32 = FStar.UInt32

include Steel.Heap
include Steel.HProp

////////////////////////////////////////////////////////////////////////////////
// Memory
////////////////////////////////////////////////////////////////////////////////
val mem : Type u#1
val locks_invariant : mem -> hprop

val heap_of_mem (x:mem) : heap

val m_disjoint: mem -> heap -> prop

val upd_joined_heap: (m:mem) -> (h:heap{m_disjoint m h}) -> mem

let hmem (fp:hprop) = m:mem{interp (fp `star` locks_invariant m) (heap_of_mem m)}



/// memories satisfying [p1 `star` p2] can be split
/// into disjoint fragments satisfying each of them
val split_mem (p1 p2:hprop) (m:hheap (p1 `star` p2))
  : Tot (ms:(hheap p1 & hheap p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
