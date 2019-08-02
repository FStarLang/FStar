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
module DelimitedRelease
open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"


let wallet (hi:ref int) (lo:ref int) (k:int) 
  : ST unit
       (requires (fun h -> h `contains_a_well_typed` hi /\
                        h `contains_a_well_typed` lo))
       (ensures (fun _ _ _ -> True)) =
  if k < !hi then begin
    hi := !hi - k;
    lo := !lo + k
  end

module S = FStar.Set
// We reason about a set of addresses so as to reuse the [modifies] clause.
type addr_set = S.set nat

let heap_equiv_on (r:ref int) (h_0:heap) (h_1:heap) =
    h_0 `contains` r /\
    h_1 `contains` r ==>
    sel h_0 r == sel h_1 r

let delimited_release_wallet (hi:ref int) (lo:ref int) (k:int)
                             (h0:heap{h0 `contains_a_well_typed` hi /\
                                      h0 `contains_a_well_typed` lo})
                             (h1:heap{h1 `contains_a_well_typed` hi /\
                                      h1`contains_a_well_typed` lo})
  : Lemma (requires (heap_equiv_on lo h0 h1 /\
                     addr_of hi <> addr_of lo /\
                     (k < sel h0 hi <==> k < sel h1 hi)))
          (ensures (let _, h0' = reify (wallet hi lo k) h0 in
                    let _, h1' = reify (wallet hi lo k) h1 in
                    heap_equiv_on lo h0' h1'))
  = ()
  
