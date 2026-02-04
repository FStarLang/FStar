(*
   Helper module for CountingSemaphore ghost operations - Implementation
*)
module Pulse.Lib.CountingSemaphore.Ghost
#lang-pulse

open Pulse.Lib.Pervasives
module GFT = Pulse.Lib.GhostFractionalTable

(* Pure F* lemma implementations - must come before Pulse functions *)

(** count_true_list is always <= length *)
let rec count_true_le_length (flags: flags_list)
  : Lemma (ensures count_true_list flags <= List.length flags)
          (decreases flags)
= match flags with
  | [] -> ()
  | _ :: tl -> count_true_le_length tl

(** If one flag at index i is false, then count_true < length *)
let rec count_true_lt_length_with_false (flags: flags_list) (i: nat)
  : Lemma (requires i < List.length flags /\ list_index flags i == false)
          (ensures count_true_list flags < List.length flags)
          (decreases flags)
= match flags with
  | [] -> ()  // impossible by precondition
  | hd :: tl ->
    if i = 0 then (
      // hd is false, count tl <= length tl, so count flags < length flags
      count_true_le_length tl
    ) else (
      count_true_lt_length_with_false tl (i - 1)
    )

(** Acquire a slot from slots_range when we know there's at least one available *)
ghost fn rec acquire_slot_aux
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo n: nat) (target: nat)
  requires slots_range p tbl flags lo **
           pure (List.length flags == n /\ target < n /\ list_index flags target == true)
  ensures slots_range p tbl (list_update flags target false) lo **
          GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target)
  decreases target
{
  if Nil? flags {
    unreachable ()
  } else {
    let hd = List.Tot.hd flags;
    let tl = List.Tot.tl flags;
    assert (pure (n > 0 /\ flags == hd :: tl));
    rewrite (slots_range p tbl flags lo) as (slots_range p tbl (hd :: tl) lo);
    unfold (slots_range p tbl (hd :: tl) lo);
    if (target = 0) {
      assert (pure (list_index (hd :: tl) 0 == hd));
      assert (pure (hd == true));
      rewrite (slot_inv p tbl hd lo) as (slot_inv p tbl true lo);
      unfold (slot_inv p tbl true lo);
      // Have: GFT.pts_to tbl lo #1.0R true ** p lo
      GFT.share tbl lo 0.5R 0.5R;
      // Now: GFT.pts_to tbl lo #0.5R true ** GFT.pts_to tbl lo #0.5R true ** p lo
      // Need to change the value from true to false for the half we keep
      GFT.gather tbl lo;
      GFT.update #bool tbl #lo #true false;
      GFT.share tbl lo 0.5R 0.5R;
      // Now: GFT.pts_to tbl lo #0.5R false ** GFT.pts_to tbl lo #0.5R false ** p lo
      fold (slot_inv p tbl false lo);
      assert (pure (list_update (hd :: tl) 0 false == false :: tl));
      fold (slots_range p tbl (false :: tl) lo);
      rewrite (slots_range p tbl (false :: tl) lo)
           as (slots_range p tbl (list_update flags target false) lo);
      assert (pure (lo + target == lo));
      rewrite (GFT.pts_to tbl lo #0.5R false ** p lo)
           as (GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target))
    } else {
      assert (pure (target - 1 < n - 1));
      assert (pure (list_index tl (target - 1) == true));
      acquire_slot_aux p tbl tl (lo + 1) (n - 1) (target - 1);
      assert (pure (lo + 1 + (target - 1) == lo + target));
      rewrite (GFT.pts_to tbl (lo + 1 + (target - 1)) #0.5R false ** p (lo + 1 + (target - 1)))
           as (GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target));
      list_update_length (hd :: tl) target false;
      assert (pure (list_update (hd :: tl) target false == hd :: list_update tl (target - 1) false));
      fold (slots_range p tbl (hd :: list_update tl (target - 1) false) lo);
      rewrite (slots_range p tbl (hd :: list_update tl (target - 1) false) lo)
           as (slots_range p tbl (list_update flags target false) lo)
    }
  }
}

(** Public acquire_slot - returns erased target *)
ghost fn acquire_slot
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo n: nat)
  requires slots_range p tbl flags lo **
           pure (count_true_list flags > 0 /\ List.length flags == n)
  returns target: erased (t:nat{t < n /\ list_index flags t == true})
  ensures slots_range p tbl (list_update flags (reveal target) false) lo **
          GFT.pts_to tbl (lo + reveal target) #0.5R false ** p (lo + reveal target)
{
  find_true_index_some flags;
  match find_true_index flags {
    Some idx -> {
      acquire_slot_aux p tbl flags lo n idx;
      hide idx
    }
    None -> {
      unreachable ()
    }
  }
}

(** Release a slot back to slots_range *)
ghost fn rec release_slot_aux
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo n: nat) (target: nat)
  requires slots_range p tbl flags lo **
           GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target) **
           pure (target < n /\ List.length flags == n /\ list_index flags target == false)
  ensures slots_range p tbl (list_update flags target true) lo
  decreases target
{
  if Nil? flags {
    unreachable ()
  } else {
    let hd = List.Tot.hd flags;
    let tl = List.Tot.tl flags;
    assert (pure (n > 0 /\ flags == hd :: tl));
    rewrite (slots_range p tbl flags lo) as (slots_range p tbl (hd :: tl) lo);
    unfold (slots_range p tbl (hd :: tl) lo);
    if (target = 0) {
      assert (pure (hd == false));
      assert (pure (lo + target == lo));
      rewrite (GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target))
           as (GFT.pts_to tbl lo #0.5R false ** p lo);
      rewrite (slot_inv p tbl hd lo) as (slot_inv p tbl false lo);
      unfold (slot_inv p tbl false lo);
      // Have: GFT.pts_to tbl lo #0.5R false ** GFT.pts_to tbl lo #0.5R false ** p lo
      GFT.gather tbl lo;
      // Have: GFT.pts_to tbl lo #1.0R false ** p lo
      GFT.update #bool tbl #lo #false true;
      // Have: GFT.pts_to tbl lo #1.0R true ** p lo
      fold (slot_inv p tbl true lo);
      assert (pure (list_update flags target true == true :: tl));
      fold (slots_range p tbl (true :: tl) lo);
      rewrite (slots_range p tbl (true :: tl) lo)
           as (slots_range p tbl (list_update flags target true) lo)
    } else {
      assert (pure (lo + 1 + (target - 1) == lo + target));
      rewrite (GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target))
           as (GFT.pts_to tbl (lo + 1 + (target - 1)) #0.5R false ** p (lo + 1 + (target - 1)));
      release_slot_aux p tbl tl (lo + 1) (n - 1) (target - 1);
      list_update_length flags target true;
      assert (pure (list_update flags target true == hd :: list_update tl (target - 1) true));
      fold (slots_range p tbl (hd :: list_update tl (target - 1) true) lo);
      rewrite (slots_range p tbl (hd :: list_update tl (target - 1) true) lo)
           as (slots_range p tbl (list_update flags target true) lo)
    }
  }
}

(** Public release_slot *)
ghost fn release_slot
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) (idx: nat{lo <= idx}) (n: nat{idx < lo + n})
  requires slots_range p tbl flags lo **
           GFT.pts_to tbl idx #0.5R false ** p idx **
           pure (List.length flags == n /\ list_index flags (idx - lo) == false)
  ensures slots_range p tbl (list_update flags (idx - lo) true) lo
{
  let target = idx - lo;
  assert (pure (idx == lo + target));
  assert (pure (target == idx - lo));
  rewrite (GFT.pts_to tbl idx #0.5R false ** p idx)
       as (GFT.pts_to tbl (lo + target) #0.5R false ** p (lo + target));
  release_slot_aux p tbl flags lo n target;
  assert (pure (list_update flags target true == list_update flags (idx - lo) true));
  rewrite (slots_range p tbl (list_update flags target true) lo)
       as (slots_range p tbl (list_update flags (idx - lo) true) lo)
}

(** 
  Helper to extract slot at given position and prove flag correlation.
  Traverses to the slot, gathers permissions to verify they match,
  then restores everything.
*)
ghost fn rec extract_slot_at_aux
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo n: nat) (target: nat)
  requires slots_range p tbl flags lo **
           GFT.pts_to tbl (lo + target) #0.5R false **
           pure (List.length flags == n /\ target < n)
  returns _: squash (list_index flags target == false)
  ensures slots_range p tbl flags lo **
          GFT.pts_to tbl (lo + target) #0.5R false
  decreases target
{
  if Nil? flags {
    unreachable ()
  } else {
    let hd = List.Tot.hd flags;
    let tl = List.Tot.tl flags;
    assert (pure (n > 0 /\ flags == hd :: tl));
    rewrite (slots_range p tbl flags lo) as (slots_range p tbl (hd :: tl) lo);
    unfold (slots_range p tbl (hd :: tl) lo);
    
    if (target = 0) {
      // At the target slot
      assert (pure (lo + target == lo));
      rewrite (GFT.pts_to tbl (lo + target) #0.5R false)
           as (GFT.pts_to tbl lo #0.5R false);
      
      // We have: slot_inv p tbl hd lo ** GFT.pts_to tbl lo #0.5R false
      // slot_inv = GFT.pts_to tbl lo #(if hd then 1.0R else 0.5R) hd ** (if hd then p lo else emp)
      // 
      // If hd == true: slot_inv has GFT.pts_to tbl lo #1.0R true
      //   Gathering with our #0.5R false would give #1.5R which is > 1.0R - contradiction!
      // If hd == false: slot_inv has GFT.pts_to tbl lo #0.5R false
      //   Gathering gives #1.0R false - valid!
      
      // Case split on hd
      if hd {
        // hd = true case: should be unreachable
        rewrite (slot_inv p tbl hd lo) as (slot_inv p tbl true lo);
        unfold (slot_inv p tbl true lo);
        // Have: GFT.pts_to tbl lo #1.0R true ** p lo ** GFT.pts_to tbl lo #0.5R false
        // Gather gives pure (true == false) which is a contradiction
        GFT.gather #bool tbl lo #1.0R #0.5R #true #false;
        // After gather: GFT.pts_to tbl lo #1.5R true ** pure (true == false) ** p lo
        // We have pure (true == false) which is false!
        unreachable ()
      } else {
        // hd = false case: this is what we expect
        rewrite (slot_inv p tbl hd lo) as (slot_inv p tbl false lo);
        unfold (slot_inv p tbl false lo);
        // Have: GFT.pts_to tbl lo #0.5R false ** GFT.pts_to tbl lo #0.5R false
        // Gather and then split to restore
        GFT.gather tbl lo;
        GFT.share tbl lo 0.5R 0.5R;
        // Restore slot_inv
        fold (slot_inv p tbl false lo);
        rewrite (slot_inv p tbl false lo) as (slot_inv p tbl hd lo);
        fold (slots_range p tbl (hd :: tl) lo);
        rewrite (slots_range p tbl (hd :: tl) lo) as (slots_range p tbl flags lo);
        rewrite (GFT.pts_to tbl lo #0.5R false) as (GFT.pts_to tbl (lo + target) #0.5R false);
        // Prove the return value
        assert (pure (list_index flags target == hd));
        assert (pure (hd == false));
        ()
      }
    } else {
      // Recurse to find the target
      assert (pure (lo + 1 + (target - 1) == lo + target));
      rewrite (GFT.pts_to tbl (lo + target) #0.5R false)
           as (GFT.pts_to tbl (lo + 1 + (target - 1)) #0.5R false);
      extract_slot_at_aux p tbl tl (lo + 1) (n - 1) (target - 1);
      rewrite (GFT.pts_to tbl (lo + 1 + (target - 1)) #0.5R false)
           as (GFT.pts_to tbl (lo + target) #0.5R false);
      // Restore slots_range
      fold (slots_range p tbl (hd :: tl) lo);
      rewrite (slots_range p tbl (hd :: tl) lo) as (slots_range p tbl flags lo);
      // The recursive call proved list_index tl (target-1) == false
      // which means list_index (hd::tl) target == list_index tl (target-1) == false
      ()
    }
  }
}

(** Public extract_slot_at *)
ghost fn extract_slot_at
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) (idx: nat{lo <= idx}) (n: nat{idx < lo + n})
  requires slots_range p tbl flags lo **
           GFT.pts_to tbl idx #0.5R false **
           pure (List.length flags == n)
  returns _: squash (list_index flags (idx - lo) == false)
  ensures slots_range p tbl flags lo **
          GFT.pts_to tbl idx #0.5R false
{
  let target = idx - lo;
  assert (pure (idx == lo + target /\ target < n));
  rewrite (GFT.pts_to tbl idx #0.5R false)
       as (GFT.pts_to tbl (lo + target) #0.5R false);
  extract_slot_at_aux p tbl flags lo n target;
  rewrite (GFT.pts_to tbl (lo + target) #0.5R false)
       as (GFT.pts_to tbl idx #0.5R false);
  ()
}

(** count_true_list flags == length flags implies all flags are true *)
let rec count_true_all_true (flags: flags_list)
  : Lemma (requires count_true_list flags == List.length flags)
          (ensures all_flags_true flags == true)
          (decreases flags)
= match flags with
  | [] -> ()
  | true :: tl -> count_true_all_true tl
  | false :: tl -> 
    // impossible case: count_true_list (false::tl) = count_true_list tl
    // but List.length (false::tl) = 1 + List.length tl
    // so count_true_list tl would need to be > List.length tl, contradiction
    count_true_le_length tl

module OR = Pulse.Lib.OnRange

(** Extract on_range from slots_range when all flags are true *)
ghost fn rec extract_on_range
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) (n: nat)
  requires slots_range p tbl flags lo **
           pure (List.length flags == n /\ all_flags_true flags == true)
  ensures OR.on_range p lo (lo + n) **
          OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo (lo + n)
  decreases n
{
  if (n = 0) {
    // flags must be [] since length flags == 0
    assert (pure (flags == []));
    assert (pure (lo + n == lo));
    rewrite (slots_range p tbl flags lo) as emp;
    OR.on_range_empty p lo;
    OR.on_range_empty (fun j -> GFT.pts_to tbl j #1.0R true) lo
  } else {
    // flags must be hd :: tl
    match flags {
      Nil -> {
        // Impossible: n > 0 but flags is empty
        unreachable ()
      }
      Cons hd tl -> {
        // hd must be true since all_flags_true flags == true
        assert (pure (hd == true));
        assert (pure (all_flags_true tl == true));
        assert (pure (List.length tl == n - 1));
        
        // Rewrite flags to hd :: tl for unfolding
        rewrite each flags as (hd :: tl);
        
        // Unfold slots_range to get slot_inv and rest
        unfold (slots_range p tbl (hd :: tl) lo);
        
        // slot_inv with hd=true gives us GFT.pts_to #1.0R true ** p lo
        unfold (slot_inv p tbl hd lo);
        rewrite (GFT.pts_to tbl lo #(if hd then 1.0R else 0.5R) hd)
             as (GFT.pts_to tbl lo #1.0R true);
        rewrite (if hd then p lo else emp) as (p lo);
        
        // Recurse on tail
        extract_on_range p tbl tl (lo + 1) (n - 1);
        
        // Now have: p lo ** GFT.pts_to tbl lo #1.0R true ** 
        //           on_range p (lo+1) (lo+n) ** on_range (GFT) (lo+1) (lo+n)
        
        // Build on_range for p
        OR.on_range_cons lo #p #(lo + 1) #(lo + n);
        
        // Build on_range for GFT
        OR.on_range_cons lo #(fun j -> GFT.pts_to tbl j #1.0R true) #(lo + 1) #(lo + n)
      }
    }
  }
}

(** Length of all_false_list *)
let rec all_false_length (n: nat)
  : Lemma (ensures List.length (all_false_list n) == n) (decreases n)
= if n = 0 then () else all_false_length (n - 1)

(** count_true of all_false_list is 0 *)
let rec all_false_count (n: nat)
  : Lemma (ensures count_true_list (all_false_list n) == 0) (decreases n)
= if n = 0 then () else all_false_count (n - 1)

(** Convert GFT entries from true to false, producing all-false slots_range *)
(** Helper: Convert GFT entries from true to false, producing all-false slots_range *)
ghost fn rec make_all_slots_false_aux
  (p: nat -> slprop) (tbl: GFT.table bool) (n: nat) (lo: nat)
  requires OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo (lo + n) **
           GFT.is_table tbl (lo + n)
  ensures slots_range p tbl (all_false_list n) lo **
          GFT.is_table tbl (lo + n)
  decreases n
{
  if (n = 0) {
    assert (pure (lo + n == lo));
    rewrite (OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo (lo + n))
         as (OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo lo);
    OR.on_range_empty_elim (fun j -> GFT.pts_to tbl j #1.0R true) lo;
    fold (slots_range p tbl ([] <: flags_list) lo);
    rewrite (slots_range p tbl ([] <: flags_list) lo) as (slots_range p tbl (all_false_list n) lo)
  } else {
    OR.on_range_uncons () #(fun j -> GFT.pts_to tbl j #1.0R true) #lo #(lo + n);
    
    // Update GFT entry from true to false
    GFT.update #bool tbl #lo #true false;
    
    // Split permission: 1.0R = 0.5R +. 0.5R
    GFT.share #bool tbl lo 0.5R 0.5R;
    drop_ (GFT.pts_to tbl lo #0.5R false);
    
    // Build slot_inv
    fold (slot_inv p tbl false lo);
    
    // Recurse
    make_all_slots_false_aux p tbl (n - 1) (lo + 1);
    
    assert (pure (all_false_list n == false :: all_false_list (n - 1)));
    fold (slots_range p tbl (false :: all_false_list (n - 1)) lo);
    rewrite (slots_range p tbl (false :: all_false_list (n - 1)) lo)
         as (slots_range p tbl (all_false_list n) lo)
  }
}

(** Convert GFT entries from true to false, producing all-false slots_range *)
ghost fn make_all_slots_false
  (p: nat -> slprop) (tbl: GFT.table bool) (n: nat)
  requires OR.on_range (fun j -> GFT.pts_to tbl j #1.0R true) 0 n **
           GFT.is_table tbl n
  ensures slots_range p tbl (all_false_list n) 0 **
          GFT.is_table tbl n
{
  make_all_slots_false_aux p tbl n 0
}
