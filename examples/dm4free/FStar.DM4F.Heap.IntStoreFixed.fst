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
module FStar.DM4F.Heap.IntStoreFixed

open FStar.Seq

let id = i:nat{i < store_size}
let heap = h:seq int{length h == store_size}

let to_id n = n

let index h i = Seq.index h i

let upd h i x = let h1 = upd h i x in assert (length h1 = store_size) ; h1

let create x = create #int store_size x

let lemma_index_upd1 s n v = lemma_index_upd1 #int s n v

let lemma_index_upd2 s n v i = lemma_index_upd2 #int s n v i

let lemma_index_create v i = lemma_index_create #int store_size v i
