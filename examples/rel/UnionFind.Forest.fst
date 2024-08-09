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
module UnionFind.Forest

open FStar.Seq
open FStar.Ghost
open FStar.OrdSet

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
module ST = FStar.DM4F.Heap.ST

type subtree_t = ordset nat (fun x y -> x <= y)

let rec set_n (n:nat) :subtree_t =
  if n = 0 then empty
  else union (singleton n) (set_n (n - 1))

type id (n:nat) = i:nat{i < n}

(*
 * each node maintains its parent id, height, and (ghost) subtree nodes (including itself)
 * the subtree is used as the decreasing metric in recursive calls
 *)
type elt (n:nat) = id n & nat & erased (subtree_t)

type uf_forest (n:nat) = s:seq (ref (elt n)){length s = n}

(* liveness and separation condition for the unionfind forest *)
let live (#n:nat) (uf:uf_forest n) (h:heap) :Type0 =
  (forall (i:id n).{:pattern addr_of (index uf i)} forall (j:id n).{:pattern addr_of (index uf j)}
               i <> j ==> addr_of (index uf i) <> addr_of (index uf j)) /\  //all the refs in the forest are distinct
  (forall (i:id n).{:pattern (h `contains_a_well_typed` (index uf i))}
               h `contains_a_well_typed` (index uf i))  //all the refs in the forest are well typed

 let get (#n:nat) (uf:uf_forest n) (i:id n)
  :ST (elt n) (requires (fun h0      -> live uf h0))
              (ensures  (fun h0 r h1 -> r == sel h0 (index uf i) /\ h0 == h1))
  = let h = ST.get () in
    sel_tot h (index uf i)

 let set (#n:nat) (uf:uf_forest n) (i:id n) (elt:elt n)
  :ST unit (requires (fun h0      -> live uf h0))
           (ensures  (fun h0 _ h1 -> h1 == upd h0 (index uf i) elt))
  = let h0 = ST.get () in
    ST.put (upd_tot h0 (index uf i) elt)
