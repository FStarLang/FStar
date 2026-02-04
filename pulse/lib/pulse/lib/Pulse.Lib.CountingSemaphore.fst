(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.CountingSemaphore
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.OnRange
open Pulse.Lib.Primitives
open Pulse.Lib.CancellableInvariant

module U32 = FStar.UInt32
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module GFT = Pulse.Lib.GhostFractionalTable
module OR = Pulse.Lib.OnRange
module CInv = Pulse.Lib.CancellableInvariant
module SemGhost = Pulse.Lib.CountingSemaphore.Ghost

(**
  Implementation using GhostFractionalTable with bool values.
  
  Key design:
  - GFT.table bool: table[i] = true means semaphore owns p i, false means client has it
  - permit p s i = GFT.pts_to tbl i #0.5R false (client half of the entry with value false)
  - slot_inv relates table entry to ownership of p i
  - slots_range builds invariant over all slots
*)

(** Build initial all-true flags list *)
let rec all_true_list (n: nat) : SemGhost.flags_list =
  if n = 0 then [] else true :: all_true_list (n - 1)

let rec all_true_length (n: nat) 
  : Lemma (ensures List.length (all_true_list n) == n) (decreases n)
= if n = 0 then () else all_true_length (n - 1)

let rec all_true_count (n: nat)
  : Lemma (ensures SemGhost.count_true_list (all_true_list n) == n) (decreases n)
= if n = 0 then () else all_true_count (n - 1)

(** Pure relation factored out for explicit fold/unfold *)
let sem_relation (n: U32.t) (flags: SemGhost.flags_list) (max: sem_max) : prop =
  List.length flags == max /\ U32.v n == SemGhost.count_true_list flags

(** Full invariant *)
let sem_inv_aux (p: nat -> slprop) (counter: B.box U32.t) (tbl: GFT.table bool) (max: sem_max) : slprop =
  exists* (n: U32.t) (flags: SemGhost.flags_list).
    B.pts_to counter n **
    GFT.is_table tbl max **
    SemGhost.slots_range p tbl flags 0 **
    pure (sem_relation n flags max)

let sem_inv p counter tbl max = sem_inv_aux p counter tbl max

[@@CAbstractStruct]
noeq
type sem_rec (p: nat -> slprop) = {
  counter: B.box U32.t;
  tbl: GFT.table bool;
  max: sem_max;
  i: cinv;
}

let sem (p: nat -> slprop) : Type0 = sem_rec p

(** Permit = half ownership of table entry with value false *)
let permit p (s: sem p) (idx: nat) : slprop =
  GFT.pts_to s.tbl idx #0.5R false ** pure (idx < s.max)

instance placeless_permit p s idx : placeless (permit p s idx) =
  placeless_star 
    (GFT.pts_to s.tbl idx #0.5R false) 
    (pure (idx < s.max))

let sem_alive p s #perm max =
  inv (iname_of s.i) (cinv_vp s.i (sem_inv p s.counter s.tbl max)) **
  active s.i perm **
  pure (s.max == max)

(** Initialize slots from on_range - creates all-true slots_range *)
ghost fn rec init_slots_from_range (p: nat -> slprop) (tbl: GFT.table bool) (n lo: nat)
  requires OR.on_range p lo (lo + n) ** 
           OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo (lo + n)
  ensures SemGhost.slots_range p tbl (all_true_list n) lo
  decreases n
{
  if (n = 0) {
    assert (pure (lo + n == lo));
    assert (pure (all_true_list n == []));
    rewrite (OR.on_range p lo (lo + n)) as (OR.on_range p lo lo);
    OR.on_range_empty_elim p lo;
    rewrite (OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo (lo + n))
         as (OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo lo);
    OR.on_range_empty_elim (fun j -> GFT.pts_to tbl j #1.0R true) lo;
    fold (SemGhost.slots_range p tbl ([] <: SemGhost.flags_list) lo);
    rewrite (SemGhost.slots_range p tbl ([] <: SemGhost.flags_list) lo) 
         as (SemGhost.slots_range p tbl (all_true_list n) lo)
  } else {
    OR.on_range_uncons () #p #lo #(lo + n);
    OR.on_range_uncons () #(fun j -> GFT.pts_to tbl j #1.0R true) #lo #(lo + n);
    // Have: p lo ** on_range p (lo+1) (lo+n) ** GFT.pts_to tbl lo #1.0R true ** on_range ... (lo+1)
    fold (SemGhost.slot_inv p tbl true lo);
    init_slots_from_range p tbl (n - 1) (lo + 1);
    assert (pure (all_true_list n == true :: all_true_list (n - 1)));
    rewrite (SemGhost.slot_inv p tbl true lo ** SemGhost.slots_range p tbl (all_true_list (n - 1)) (lo + 1))
         as (SemGhost.slots_range p tbl (all_true_list n) lo)
  }
}

(** Allocate table slots with initial value true *)
ghost fn rec alloc_slots (tbl: GFT.table bool) (cur max_val: nat)
  requires GFT.is_table tbl cur ** pure (cur <= max_val)
  ensures GFT.is_table tbl max_val ** OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) cur max_val
  decreases (max_val - cur)
{
  if (cur = max_val) {
    OR.on_range_empty (fun j -> GFT.pts_to tbl j #1.0R true) cur
  } else {
    GFT.alloc tbl true;
    alloc_slots tbl (cur + 1) max_val;
    OR.on_range_cons cur #(fun j -> GFT.pts_to tbl j #1.0R true) #(cur + 1) #max_val
  }
}

fn new_sem (p: nat -> slprop) {| d: (k:nat) -> is_send (p k) |} (max: sem_max)
  requires OR.on_range p 0 max
  returns s: sem p
  ensures sem_alive p s max
{
  let counter = B.alloc (U32.uint_to_t max);
  let tbl = GFT.create #bool;
  alloc_slots tbl 0 max;
  init_slots_from_range p tbl max 0;
  
  all_true_length max;
  all_true_count max;
  
  fold (sem_inv_aux p counter tbl max);
  fold (sem_inv p counter tbl max);
  
  let i = new_cancellable_invariant (sem_inv p counter tbl max);
  let s : sem p = { counter; tbl; max; i };
  rewrite each counter as s.counter, tbl as s.tbl, i as s.i;
  fold (sem_alive p s #1.0R max);
  s
}

(** Read counter value through invariant - basic version *)
fn read_counter (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p)
  preserves sem_alive p s #perm max
  returns v: U32.t
  ensures emp
{
  unfold (sem_alive p s #perm max);
  
  let result =
    with_invariants U32.t emp_inames (CInv.iname_of s.i)
        (cinv_vp s.i (sem_inv p s.counter s.tbl s.max))
        (active s.i perm)
        (fun _ -> active s.i perm)
    fn _ {
      unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.tbl s.max);
      unfold (sem_inv_aux p s.counter s.tbl s.max);
      
      with n flags. _;
      
      let v = read_atomic_box s.counter;
      
      fold (sem_inv_aux p s.counter s.tbl s.max);
      fold (sem_inv p s.counter s.tbl s.max);
      pack_cinv_vp s.i;
      v
    };
  
  fold (sem_alive p s #perm max);
  result
}

(** Read counter for release - proves counter < max when holding a permit *)
fn read_counter_for_release (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p) (idx: nat { idx < max })
  requires sem_alive p s #perm max ** GFT.pts_to s.tbl idx #0.5R false ** pure (idx < s.max)
  returns v: (v:U32.t{U32.v v < max})
  ensures sem_alive p s #perm max ** GFT.pts_to s.tbl idx #0.5R false ** pure (idx < s.max)
{
  unfold (sem_alive p s #perm max);
  
  let result : (v:U32.t{U32.v v < max}) =
    with_invariants (v:U32.t{U32.v v < max}) emp_inames (CInv.iname_of s.i)
        (cinv_vp s.i (sem_inv p s.counter s.tbl s.max))
        (active s.i perm ** GFT.pts_to s.tbl idx #0.5R false ** pure (idx < s.max))
        (fun _ -> active s.i perm ** GFT.pts_to s.tbl idx #0.5R false ** pure (idx < s.max))
    fn _ {
      unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.tbl s.max);
      unfold (sem_inv_aux p s.counter s.tbl s.max);
      
      with n flags. _;
      
      // Use extract_slot_at to prove that the flag at idx is false
      let _ = SemGhost.extract_slot_at p s.tbl flags 0 idx max;
      // Now we know: list_index flags idx == false
      
      // Since flag at idx is false and length flags == max, 
      // count_true_list flags < length flags == max
      // And U32.v n == count_true_list flags
      // Therefore U32.v n < max
      SemGhost.count_true_lt_length_with_false flags idx;
      
      let v = read_atomic_box s.counter;
      // v == n, and U32.v n < max, so U32.v v < max
      
      fold (sem_inv_aux p s.counter s.tbl s.max);
      fold (sem_inv p s.counter s.tbl s.max);
      pack_cinv_vp s.i;
      v
    };
  
  fold (sem_alive p s #perm max);
  intro_pure (idx < s.max) ();
  result
}

(** Try to acquire a slot *)
fn try_acquire (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p)
  preserves sem_alive p s #perm max
  returns b: bool
  ensures cond b (exists* (i:nat{i < max}). permit p s i ** p i) emp
{
  // Read counter outside
  let v = read_counter #p #perm #max s;
  
  if (v = 0ul) {
    // No available slots
    intro_cond_false (exists* (i:nat{i < max}). permit p s i ** p i) emp;
    false
  } else {
    unfold (sem_alive p s #perm max);
    
    // Try to acquire - CAS from v to v-1
    let new_v : U32.t = U32.sub v 1ul;
    
    // Result type: just a boolean, resources tracked in postcondition via existential
    let result : bool =
      with_invariants bool emp_inames (CInv.iname_of s.i)
          (cinv_vp s.i (sem_inv p s.counter s.tbl s.max))
          (active s.i perm ** pure (U32.v v > 0 /\ s.max == max))
          (fun b -> 
            active s.i perm ** pure (s.max == max) **
            cond b (exists* (i:nat{i < max}). GFT.pts_to s.tbl i #0.5R false ** p i) emp)
      fn _ {
        unpack_cinv_vp s.i;
        unfold (sem_inv p s.counter s.tbl s.max);
        unfold (sem_inv_aux p s.counter s.tbl s.max);
        
        with n flags. _;
        
        // Try CAS from v to v-1
        let b = cas_box s.counter v new_v;
        
        if b {
          elim_cond_true _ _ _;
          // CAS succeeded! n was v, counter now is new_v
          rewrite each n as v;
          
          // Use external ghost function to acquire slot - returns erased target
          let target = SemGhost.acquire_slot p s.tbl flags 0 max;
          
          // Update invariant with new flags
          SemGhost.count_true_update_to_false flags (reveal target);
          SemGhost.list_update_length flags (reveal target) false;
          
          fold (sem_inv_aux p s.counter s.tbl s.max);
          fold (sem_inv p s.counter s.tbl s.max);
          pack_cinv_vp s.i;
          
          // We have: GFT.pts_to s.tbl (0 + reveal target) #0.5R false ** p (0 + reveal target)
          assert (pure (0 + reveal target == reveal target /\ reveal target < max /\ reveal target < s.max));
          rewrite (GFT.pts_to s.tbl (0 + reveal target) #0.5R false ** p (0 + reveal target))
               as (GFT.pts_to s.tbl (reveal target) #0.5R false ** p (reveal target));
          
          // Introduce existential with the acquired resources
          intro_exists (fun (i:nat{i < max}) -> GFT.pts_to s.tbl i #0.5R false ** p i) (reveal target);
          fold (cond true (exists* (i:nat{i < max}). GFT.pts_to s.tbl i #0.5R false ** p i) emp);
          true
        } else {
          elim_cond_false _ _ _;
          // CAS failed, put invariant back unchanged
          fold (sem_inv_aux p s.counter s.tbl s.max);
          fold (sem_inv p s.counter s.tbl s.max);
          pack_cinv_vp s.i;
          intro_cond_false (exists* (i:nat{i < max}). GFT.pts_to s.tbl i #0.5R false ** p i) emp;
          false
        }
      };
    
    fold (sem_alive p s #perm max);
    
    if result {
      rewrite (cond result (exists* (i:nat{i < max}). GFT.pts_to s.tbl i #0.5R false ** p i) emp)
           as (exists* (i:nat{i < max}). GFT.pts_to s.tbl i #0.5R false ** p i);
      // Repackage with permit
      with target. _;
      fold (permit p s target);
      intro_exists (fun (i:nat{i < max}) -> permit p s i ** p i) target;
      intro_cond_true (exists* (i:nat{i < max}). permit p s i ** p i) emp;
      true
    } else {
      rewrite (cond result (exists* (i:nat{i < max}). GFT.pts_to s.tbl i #0.5R false ** p i) emp) as emp;
      intro_cond_false (exists* (i:nat{i < max}). permit p s i ** p i) emp;
      false
    }
  }
}

(** Release a slot back to the semaphore - recursive helper *)
fn rec release_loop (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p) (idx: nat { idx < max })
  requires sem_alive p s #perm max ** GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max)
  ensures sem_alive p s #perm max
{
  // Read counter outside invariant - this proves v < max since we hold a permit
  intro_pure (idx < s.max) ();
  let v = read_counter_for_release #p #perm #max s idx;
  // v < max, so v + 1 <= max <= U32.max_int (since max: sem_max, i.e., max <= U32.max_int)
  // Therefore v + 1 won't overflow
  let new_v : U32.t = U32.add v 1ul;
  
  unfold (sem_alive p s #perm max);
  
  let result : bool =
    with_invariants bool emp_inames (CInv.iname_of s.i)
        (cinv_vp s.i (sem_inv p s.counter s.tbl s.max))
        (active s.i perm ** pure (s.max == max) ** GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max))
        (fun b -> active s.i perm ** cond b emp (GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max)))
    fn _ {
      unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.tbl s.max);
      unfold (sem_inv_aux p s.counter s.tbl s.max);
      
      with n flags. _;
      
      // Try CAS from v to v+1
      let b = cas_box s.counter v new_v;
      
      if b {
        elim_cond_true b _ _;
        // CAS succeeded! n was v, counter now is v+1
        rewrite each n as v;
        
        // Use extract_slot_at to prove flag correlation
        let _ = SemGhost.extract_slot_at p s.tbl flags 0 idx max;
        
        // Now we can call release_slot
        SemGhost.release_slot p s.tbl flags 0 idx max;
        SemGhost.count_true_update_to_true flags idx;
        SemGhost.list_update_length flags idx true;
        
        fold (sem_inv_aux p s.counter s.tbl s.max);
        fold (sem_inv p s.counter s.tbl s.max);
        pack_cinv_vp s.i;
        
        fold (cond true emp (GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max)));
        true
      } else {
        elim_cond_false b _ _;
        // CAS failed, put invariant back unchanged
        fold (sem_inv_aux p s.counter s.tbl s.max);
        fold (sem_inv p s.counter s.tbl s.max);
        pack_cinv_vp s.i;
        fold (cond false emp (GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max)));
        false
      }
    };
  
  fold (sem_alive p s #perm max);
  
  if result {
    elim_cond_true result emp (GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max));
    ()
  } else {
    elim_cond_false result emp (GFT.pts_to s.tbl idx #0.5R false ** p idx ** pure (idx < s.max));
    intro_pure (idx < s.max) ();
    release_loop #p #perm #max s idx
  }
}

(** Release a slot back to the semaphore *)
fn release (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p) (idx: nat { idx < max })
  preserves sem_alive p s #perm max
  requires permit p s idx ** p idx
  ensures emp
{
  unfold (permit p s idx);
  // Have: GFT.pts_to s.tbl idx #0.5R false ** pure (idx < s.max) ** p idx ** sem_alive p s #perm max
  release_loop #p #perm #max s idx
}

(** Share permission on sem_alive *)
ghost fn share (#p: nat -> slprop) (#perm: perm) (#max: sem_max) (s: sem p)
  requires sem_alive p s #perm max
  ensures sem_alive p s #(perm /. 2.0R) max ** sem_alive p s #(perm /. 2.0R) max
{
  unfold (sem_alive p s #perm max);
  CInv.share s.i;
  dup_inv (iname_of s.i) (cinv_vp s.i (sem_inv p s.counter s.tbl max));
  fold (sem_alive p s #(perm /. 2.0R) max);
  fold (sem_alive p s #(perm /. 2.0R) max)
}

(** Gather permission on sem_alive *)
ghost fn gather (#p: nat -> slprop) (#perm1 #perm2: perm) (#max: sem_max) (s: sem p)
  requires sem_alive p s #perm1 max ** sem_alive p s #perm2 max
  ensures sem_alive p s #(perm1 +. perm2) max
{
  unfold (sem_alive p s #perm1 max);
  unfold (sem_alive p s #perm2 max);
  CInv.gather s.i;
  drop_ (inv (iname_of s.i) (cinv_vp s.i (sem_inv p s.counter s.tbl max)));
  fold (sem_alive p s #(perm1 +. perm2) max)
}

(** Try to free the semaphore - CAS counter from max to 0, atomically acquire all permits *)
fn try_free (#p: nat -> slprop) (#max: sem_max) (s: sem p)
  requires sem_alive p s #1.0R max
  returns b: bool
  ensures cond b (OR.on_range p 0 max) (sem_alive p s #1.0R max)
{
  unfold (sem_alive p s #1.0R max);
  
  let max_u32 : U32.t = U32.uint_to_t max;
  
  // Try to CAS counter from max to 0 inside the invariant
  // If successful, extract on_range and leave invariant with empty slots_range
  let result : bool =
    with_invariants bool emp_inames (CInv.iname_of s.i)
        (cinv_vp s.i (sem_inv p s.counter s.tbl s.max))
        (active s.i 1.0R ** pure (s.max == max))
        (fun b -> active s.i 1.0R ** cond b (OR.on_range p 0 max) emp)
    fn _ {
      unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.tbl s.max);
      unfold (sem_inv_aux p s.counter s.tbl s.max);
      
      with n flags. _;
      
      // Try CAS from max to 0
      let b = cas_box s.counter max_u32 0ul;
      
      if b {
        elim_cond_true b _ _;
        // CAS succeeded! counter was max (all permits available), now 0
        rewrite each n as max_u32;
        
        // Since counter was max, count_true_list flags == max == length flags
        // Therefore all flags are true
        SemGhost.count_true_all_true flags;
        
        // Extract on_range from slots_range (all flags true)
        SemGhost.extract_on_range p s.tbl flags 0 max;
        
        // Now we have:
        // - on_range p 0 max (to return to caller)
        // - on_range (GFT.pts_to tbl j #1.0R true) 0 max
        // - B.pts_to s.counter 0ul
        // - GFT.is_table s.tbl max
        
        // We need to put back the invariant with counter=0 and all-false flags
        // slots_range with all-false flags is emp (no p i owned)
        // But we need to update the GFT entries from true to false
        
        // Actually, we need to build a new slots_range with all false flags
        // This requires updating each GFT entry and creating the new flags list
        
        // For now, we'll use a ghost function to convert all-true slots to all-false
        // Since all flags are true, each slot_inv has GFT.pts_to #1.0R true ** p i
        // We extracted p i via extract_on_range
        // We still have GFT.pts_to #1.0R true for each slot
        // We can update them to false and create slots_range with all-false flags
        
        // Update all GFT entries from true to false
        SemGhost.make_all_slots_false p s.tbl max;
        
        // Now we have slots_range with all-false flags
        // Prove sem_relation for the new state: counter=0, all_false_list max flags
        SemGhost.all_false_length max;
        SemGhost.all_false_count max;
        // Now: List.length (all_false_list max) == max == s.max
        //      count_true_list (all_false_list max) == 0 == U32.v 0ul
        // So sem_relation 0ul (all_false_list max) s.max holds
        
        // Restore the invariant with counter=0, all-false flags
        fold (sem_inv_aux p s.counter s.tbl s.max);
        fold (sem_inv p s.counter s.tbl s.max);
        pack_cinv_vp s.i;
        
        fold (cond true (OR.on_range p 0 max) emp);
        true
      } else {
        elim_cond_false b _ _;
        // CAS failed, restore invariant unchanged
        fold (sem_inv_aux p s.counter s.tbl s.max);
        fold (sem_inv p s.counter s.tbl s.max);
        pack_cinv_vp s.i;
        fold (cond false (OR.on_range p 0 max) emp);
        false
      }
    };
  
  if result {
    // CAS succeeded - we have on_range p 0 max, can cancel invariant
    elim_cond_true result _ _;
    
    // Buy a later credit for cancel
    later_credit_buy 1;
    
    // Cancel the invariant
    CInv.cancel s.i;
    
    // The cancelled invariant content is sem_inv with counter=0, all-false flags
    unfold (sem_inv p s.counter s.tbl s.max);
    unfold (sem_inv_aux p s.counter s.tbl s.max);
    with n flags. _;
    
    // Free the counter box
    B.free s.counter;
    
    // Drop ghost resources
    drop_ (SemGhost.slots_range p s.tbl flags 0);
    drop_ (GFT.is_table s.tbl s.max);
    
    intro_cond_true (OR.on_range p 0 max) (sem_alive p s #1.0R max);
    true
  } else {
    // CAS failed - restore sem_alive
    elim_cond_false result _ _;
    fold (sem_alive p s #1.0R max);
    intro_cond_false (OR.on_range p 0 max) (sem_alive p s #1.0R max);
    false
  }
}
