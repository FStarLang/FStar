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
open FStar.FunctionalExtensionality

friend Steel.Heap
friend Steel.HProp

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"


////////////////////////////////////////////////////////////////////////////////
// allocation and locks
////////////////////////////////////////////////////////////////////////////////
noeq
type lock_state =
  | Available : hprop -> lock_state
  | Locked    : hprop -> lock_state

let _ : squash (inversion lock_state) = allow_inversion lock_state

let lock_store = list lock_state

#push-options "--max_ifuel 1 --initial_ifuel 1"
let rec lock_store_invariant (l:lock_store) : hprop =
  match l with
  | [] -> emp
  | Available h :: tl -> h `star` lock_store_invariant tl
  | _ :: tl -> lock_store_invariant tl
#pop-options

noeq
type mem = {
  ctr: nat;
  heap: heap;
  locks: lock_store;
  properties: squash (
    (forall i. i >= ctr ==> heap i == None) /\
    interp (lock_store_invariant locks) heap
  )
}

let _ : squash (inversion mem) = allow_inversion mem

let locks_invariant (m:mem) : hprop = lock_store_invariant m.locks

let heap_of_mem (x:mem) : heap = x.heap

let m_disjoint (m:mem) (h:heap) =
  disjoint (heap_of_mem m) h /\
  (forall i. i >= m.ctr ==> h i == None)

let upd_joined_heap (m:mem) (h:heap{m_disjoint m h}) =
  let h0 = heap_of_mem m in
  let h = join h0 h in
  {m with heap = h}


/// F*'s indefinite_description is only available in the Ghost effect
/// That's to prevent us from mistakenly extracting code that uses the
/// axiom, since, clearly, we can't execute code that invents witnesses
/// from squashed proofs of existentials.
///
/// Here, we're just building a logical model of heaps, so I don't really
/// care about enforcing the ghostiness of indefinite_description.
///
/// So, this axiom explicitly punches a hole in the ghost effect, allowing
/// me to coerce it to Tot
assume
val axiom_ghost_to_tot (#a:Type) (#b:a -> Type) ($f: (x:a -> GTot (b x))) (x:a)
  : Tot (b x)

let split_mem (p1 p2:hprop) (m:hheap (p1 `Star` p2))
  : Tot (ms:(hheap p1 & hheap p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = axiom_ghost_to_tot (split_mem_ghost p1 p2) m
