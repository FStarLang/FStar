(*
   Helper module for CountingSemaphore ghost operations
   
   Design:
   - GFT stores bool values: true = available, false = handed out
   - Table contents correlate with flags list in invariant
   - permit holds half permission to table entry with value false
*)
module Pulse.Lib.CountingSemaphore.Ghost
#lang-pulse

open Pulse.Lib.Pervasives
module GFT = Pulse.Lib.GhostFractionalTable

(** Flags list type *)
type flags_list = list bool

(** Count true values in a list *)
let rec count_true_list (flags: flags_list) : nat =
  match flags with
  | [] -> 0
  | true :: tl -> 1 + count_true_list tl
  | false :: tl -> count_true_list tl

(** Update list at position i *)
let rec list_update (l: flags_list) (i: nat) (v: bool) : flags_list =
  match l with
  | [] -> []
  | hd :: tl -> if i = 0 then v :: tl else hd :: list_update tl (i - 1) v

(** Index into a list *)
let rec list_index (l: flags_list) (i: nat) : bool =
  match l with  
  | [] -> false
  | hd :: tl -> if i = 0 then hd else list_index tl (i - 1)

(** Find first true index *)
let rec find_true_index (flags: flags_list)
  : Tot (option (i:nat{i < List.length flags /\ list_index flags i == true}))
        (decreases flags)
= match flags with
  | [] -> None
  | true :: tl -> Some 0
  | false :: tl -> 
    match find_true_index tl with
    | None -> None
    | Some i -> Some (i + 1)

(** Lemmas *)
let rec list_update_length (l: flags_list) (i: nat) (v: bool)
  : Lemma (ensures List.length (list_update l i v) == List.length l)
          (decreases l)
= match l with
  | [] -> ()
  | _ :: tl -> if i = 0 then () else list_update_length tl (i - 1) v

let rec count_true_update_to_false (flags: flags_list) (i: nat)
  : Lemma (requires i < List.length flags /\ list_index flags i == true)
          (ensures count_true_list (list_update flags i false) == count_true_list flags - 1)
          (decreases flags)
= match flags with
  | [] -> ()
  | hd :: tl -> 
    if i = 0 then ()
    else count_true_update_to_false tl (i - 1)

let rec count_true_update_to_true (flags: flags_list) (i: nat)
  : Lemma (requires i < List.length flags /\ list_index flags i == false)
          (ensures count_true_list (list_update flags i true) == count_true_list flags + 1)
          (decreases flags)
= match flags with
  | [] -> ()
  | hd :: tl ->
    if i = 0 then ()
    else count_true_update_to_true tl (i - 1)

let rec find_true_index_some (flags: flags_list)
  : Lemma (ensures count_true_list flags > 0 <==> Some? (find_true_index flags))
          (decreases flags)
= match flags with
  | [] -> ()
  | true :: _ -> ()
  | false :: tl -> find_true_index_some tl

let rec list_update_index (l: flags_list) (i: nat) (v: bool)
  : Lemma (requires i < List.length l)
          (ensures list_index (list_update l i v) i == v)
          (decreases l)
= match l with
  | [] -> ()
  | _ :: tl -> if i = 0 then () else list_update_index tl (i - 1) v

let rec list_update_other (l: flags_list) (i j: nat) (v: bool)
  : Lemma (requires i < List.length l /\ j < List.length l /\ i <> j)
          (ensures list_index (list_update l i v) j == list_index l j)
          (decreases l)
= match l with
  | [] -> ()
  | _ :: tl -> 
    if i = 0 then ()
    else if j = 0 then ()
    else list_update_other tl (i - 1) (j - 1) v

(** count_true_list is always <= length *)
val count_true_le_length (flags: flags_list)
  : Lemma (ensures count_true_list flags <= List.length flags)

(** If one flag at index i is false, then count_true < length *)
val count_true_lt_length_with_false (flags: flags_list) (i: nat)
  : Lemma (requires i < List.length flags /\ list_index flags i == false)
          (ensures count_true_list flags < List.length flags)

(** Per-slot predicate: relates GFT entry to flag *)
let slot_inv (p: nat -> slprop) (tbl: GFT.table bool) (flag: bool) (i: nat) : slprop =
  GFT.pts_to tbl i #(if flag then 1.0R else 0.5R) flag **
  (if flag then p i else emp)

(** Range of slots with flags *)
let rec slots_range (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) : slprop =
  match flags with
  | [] -> emp
  | hd :: tl -> slot_inv p tbl hd lo ** slots_range p tbl tl (lo + 1)

(** Acquire a slot - returns erased target *)
val acquire_slot
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo n: nat)
: stt_ghost (erased (target:nat{target < n /\ list_index flags target == true})) emp_inames
    (slots_range p tbl flags lo **
     pure (count_true_list flags > 0 /\ List.length flags == n))
    (fun target -> 
     slots_range p tbl (list_update flags (reveal target) false) lo **
     GFT.pts_to tbl (lo + reveal target) #0.5R false ** p (lo + reveal target))

(** Release a slot *)
val release_slot
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) (idx: nat{lo <= idx}) (n: nat{idx < lo + n})
: stt_ghost unit emp_inames
    (slots_range p tbl flags lo **
     GFT.pts_to tbl idx #0.5R false ** p idx **
     pure (List.length flags == n /\ list_index flags (idx - lo) == false))
    (fun _ -> slots_range p tbl (list_update flags (idx - lo) true) lo)

(** 
  Extract slot at idx from slots_range and prove flag correlation.
  If we have GFT.pts_to tbl idx #0.5R false (from permit), then the flag must be false.
  This is because:
  - If flag were true, slot_inv would have GFT.pts_to tbl idx #1.0R true
  - Gathering 0.5R false with any permission of value true is impossible
  - Therefore flag must be false, and slot_inv has GFT.pts_to tbl idx #0.5R false
*)
val extract_slot_at
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) (idx: nat{lo <= idx}) (n: nat{idx < lo + n})
: stt_ghost (squash (list_index flags (idx - lo) == false)) emp_inames
    (slots_range p tbl flags lo **
     GFT.pts_to tbl idx #0.5R false **
     pure (List.length flags == n))
    (fun _ -> 
     slots_range p tbl flags lo **
     GFT.pts_to tbl idx #0.5R false)

(** Check if all flags are true *)
let rec all_flags_true (flags: flags_list) : bool =
  match flags with
  | [] -> true
  | hd :: tl -> hd && all_flags_true tl

(** If count_true_list flags == length flags, then all flags are true *)
val count_true_all_true (flags: flags_list)
  : Lemma (requires count_true_list flags == List.length flags)
          (ensures all_flags_true flags == true)

(** Extract on_range from slots_range when all flags are true *)
val extract_on_range
  (p: nat -> slprop) (tbl: GFT.table bool) (flags: flags_list) (lo: nat) (n: nat)
: stt_ghost unit emp_inames
    (slots_range p tbl flags lo **
     pure (List.length flags == n /\ all_flags_true flags == true))
    (fun _ ->
     Pulse.Lib.OnRange.on_range p lo (lo + n) **
     Pulse.Lib.OnRange.on_range (fun j -> GFT.pts_to tbl j #1.0R true) lo (lo + n))

(** Build all-false flags list *)
let rec all_false_list (n: nat) : flags_list =
  if n = 0 then [] else false :: all_false_list (n - 1)

(** Length of all_false_list *)
val all_false_length (n: nat)
  : Lemma (ensures List.length (all_false_list n) == n)

(** count_true of all_false_list is 0 *)
val all_false_count (n: nat)
  : Lemma (ensures count_true_list (all_false_list n) == 0)

(** Convert GFT entries from true to false, producing all-false slots_range *)
val make_all_slots_false
  (p: nat -> slprop) (tbl: GFT.table bool) (n: nat)
: stt_ghost unit emp_inames
    (Pulse.Lib.OnRange.on_range (fun j -> GFT.pts_to tbl j #1.0R true) 0 n **
     GFT.is_table tbl n)
    (fun _ ->
     slots_range p tbl (all_false_list n) 0 **
     GFT.is_table tbl n)
