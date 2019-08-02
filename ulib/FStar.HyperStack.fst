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
module FStar.HyperStack

include FStar.Monotonic.HyperStack

type reference (a:Type) = mreference a (Heap.trivial_preorder a)

let stackref (a:Type) = mstackref a (Heap.trivial_preorder a)
let ref (a:Type) = mref a (Heap.trivial_preorder a)

let mmstackref (a:Type) = mmmstackref a (Heap.trivial_preorder a)
let mmref (a:Type) = mmmref a (Heap.trivial_preorder a)
type s_ref (i:rid) (a:Type) = s_mref i a (Heap.trivial_preorder a)

(* Two references with different reads are disjoint. *)

let reference_distinct_sel_disjoint
  (#a:Type0) (h: mem) (r1: reference a) (r2: reference a)
: Lemma
  (requires (
    h `contains` r1 /\
    h `contains` r2 /\
    frameOf r1 == frameOf r2 /\
    as_addr r1 == as_addr r2
  ))
  (ensures (
    sel h r1 == sel h r2
  ))
= mreference_distinct_sel_disjoint h r1 r2
