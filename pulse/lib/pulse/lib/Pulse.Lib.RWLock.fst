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

module Pulse.Lib.RWLock
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Primitives
open Pulse.Lib.CancellableInvariant

module U32 = FStar.UInt32
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module CInv = Pulse.Lib.CancellableInvariant
module GFT = Pulse.Lib.GhostFractionalTable
module OR = Pulse.Lib.OnRange

///
/// Reader-Writer Lock Implementation using GhostFractionalTable
///
/// Uses an atomic counter stored in a box:
/// - 0: unlocked, full permission (pred 1.0R) is available
/// - n (0 < n < WRITER_SENTINEL): n readers have acquired
/// - WRITER_SENTINEL (0xFFFFFFFF): a writer has exclusive access
///
/// Permission accounting using GhostFractionalTable:
/// - perm_table: stores each reader's permission fraction
/// - Invariant holds 0.5R of each active entry
/// - Reader tokens hold 0.5R of their entry
/// - ghost_avail: available fraction in lock
/// - Sum of all reader fractions + avail = 1.0R
///

let max_u32 : U32.t = 0xFFFFFFFFul
let writer_sentinel : U32.t = max_u32

/// Safe reader count limit (to prevent overflow when incrementing)
let max_readers : (n:U32.t{U32.v n < U32.v writer_sentinel - 1}) = 0xFFFFFFFDul

/// Helper lemma: use fractional property to split
let fractional_split_lemma (p : perm -> slprop) (f1 f2 : perm) 
  : Lemma (requires fractional p)
          (ensures p (f1 +. f2) == (p f1 ** p f2))
  = ()

/// Helper lemma: use fractional property to combine (reverse direction)
let fractional_combine_lemma (p : perm -> slprop) (f1 f2 : perm) 
  : Lemma (requires fractional p)
          (ensures (p f1 ** p f2) == p (f1 +. f2))
  = ()

/// Helper lemma: half + half = whole
let half_plus_half (f : perm) : Lemma (f /. 2.0R +. f /. 2.0R == f) = ()

/// Helper lemma: if x <> 0 and x <> sentinel, then x - 1 <> sentinel
/// (because sentinel = max_u32, and x - 1 < x <= sentinel - 1 < sentinel)
let sub_preserves_not_sentinel (x : U32.t) : Lemma 
  (requires x <> 0ul /\ x <> writer_sentinel)
  (ensures U32.sub x 1ul <> writer_sentinel)
  = ()

/// Helper lemma: expected <= max_readers implies expected <> writer_sentinel
let expected_not_sentinel (x : U32.t) : Lemma
  (requires U32.v x <= U32.v max_readers)
  (ensures x <> writer_sentinel)
  = ()

/// Helper lemma: 0 < n < writer_sentinel implies n <> writer_sentinel
let release_expected_not_sentinel (x : U32.t) : Lemma
  (requires U32.v x > 0 /\ U32.v x < U32.v writer_sentinel)
  (ensures x <> writer_sentinel)
  = ()

//
// Lock invariant (from RWLockMine.fst)
//

let frac = r:real { r >=. 0.0R }
module Set = FStar.FiniteSet.Base

let index_set = Set.set nat

let rec total_frac (tab : nat -> frac) (entries:index_set) 
: Tot frac (decreases Set.cardinality entries)
= Set.all_finite_set_facts_lemma();
  if Set.cardinality entries = 0
  then 0.0R
  else
    let i = Set.choose entries in
    let rest = Set.remove i entries in
    tab i +. total_frac tab rest

//table of reader entries, storing the frac owned by each reader
let table_spec = nat -> frac

let table_spec_well_formed (tab:table_spec) (size:nat) (entries:index_set) =
  (forall i. i >= size \/ not (i `Set.mem` entries) ==> tab i == 0.0R) /\ //table is non-zero at most at entries
  (forall i. i `Set.mem` entries ==> i < size) /\ //all entries are within table bounds
  total_frac tab entries <. 1.0R //and sums up to less than 1.0R

let remove_element (i:nat) (entries:index_set) : index_set =
  Set.remove i entries

let rec total_frac_sum (tab:nat -> frac) (i:nat) (entries:index_set)
: Lemma 
  (requires i `Set.mem` entries)
  (ensures total_frac tab entries == tab i +. total_frac tab (remove_element i entries))
  (decreases Set.cardinality entries)
= Set.all_finite_set_facts_lemma();
  if Set.cardinality entries = 0
  then ()
  else
    let j = Set.choose entries in
    if i = j then ()
    else (
      let rest = Set.remove j entries in
      total_frac_sum tab i rest;
      calc (==) {
        total_frac tab entries;
      (==)  {}
        tab j +. (tab i +. total_frac tab (remove_element i rest));
      (==)  {}
        tab i +. (tab j +. total_frac tab (remove_element i rest));
      (==)  {}
        tab i +. (tab j +. total_frac tab (remove_element i (remove_element j entries)));
      (==)  { assert (remove_element i rest `Set.equal` remove_element j (remove_element i entries)) }
        tab i +. (tab j +. total_frac tab (remove_element j (remove_element i entries)));
      (==) { total_frac_sum tab j (remove_element i entries) }
        tab i +. total_frac tab (remove_element i entries);
      };
     ()
    )

/// Helper lemma: total_frac with inserted element
let rec total_frac_insert_fresh (tab:table_spec) (entries:index_set) (i:nat)
: Lemma 
  (requires not (i `Set.mem` entries))
  (ensures total_frac tab (Set.insert i entries) == tab i +. total_frac tab entries)
  (decreases Set.cardinality entries)
= Set.all_finite_set_facts_lemma ();
  if Set.cardinality entries = 0 then ()
  else begin
    let j = Set.choose entries in
    let rest = Set.remove j entries in
    // Set.insert i entries has j in it
    assert (j `Set.mem` (Set.insert i entries));
    total_frac_sum tab j (Set.insert i entries);
    // So total_frac tab (Set.insert i entries) = tab j + total_frac tab (Set.remove j (Set.insert i entries))
    // Set.remove j (Set.insert i entries) = Set.insert i (Set.remove j entries) = Set.insert i rest
    assert (Set.remove j (Set.insert i entries) `Set.equal` Set.insert i rest);
    // total_frac tab (Set.insert i entries) = tab j + total_frac tab (Set.insert i rest)
    // Recursively: total_frac tab (Set.insert i rest) = tab i + total_frac tab rest
    total_frac_insert_fresh tab rest i;
    // So total_frac tab (Set.insert i entries) = tab j + tab i + total_frac tab rest
    // And total_frac tab entries = tab j + total_frac tab rest
    // So total_frac tab (Set.insert i entries) = tab i + total_frac tab entries
    ()
  end

/// Helper lemma: total_frac is extensional
let rec total_frac_extensional (tab1 tab2:table_spec) (entries:index_set)
: Lemma 
  (requires forall i. i `Set.mem` entries ==> tab1 i == tab2 i)
  (ensures total_frac tab1 entries == total_frac tab2 entries)
  (decreases Set.cardinality entries)
= Set.all_finite_set_facts_lemma ();
  if Set.cardinality entries = 0 then ()
  else begin
    let i = Set.choose entries in
    let rest = Set.remove i entries in
    total_frac_extensional tab1 tab2 rest
  end

/// Helper lemma: new_spec agrees with spec on positions < table_size
let new_spec_agrees_below (spec:table_spec) (table_size:nat) (half_f:frac)
: Lemma (let new_spec = (fun i -> if i = table_size then half_f else spec i) in
         forall (k:nat). k < table_size ==> new_spec k == spec k)
= ()

/// Helper lemma: table_spec_well_formed for extended spec
let table_spec_well_formed_extend (spec:table_spec) (table_size:nat) (entries:index_set) (f:perm) (half_f:frac)
: Lemma 
  (requires 
    table_spec_well_formed spec table_size entries /\
    total_frac spec entries +. f == 1.0R /\
    half_f == f /. 2.0R /\
    half_f >. 0.0R /\
    spec table_size == 0.0R)
  (ensures
    (let new_spec = (fun i -> if i = table_size then half_f else spec i) in
     let new_entries = Set.insert table_size entries in
     let new_table_size = table_size + 1 in
     table_spec_well_formed new_spec new_table_size new_entries /\
     total_frac new_spec new_entries +. half_f == 1.0R))
= Set.all_finite_set_facts_lemma ();
  let new_spec = (fun i -> if i = table_size then half_f else spec i) in
  let new_entries = Set.insert table_size entries in
  let new_table_size = table_size + 1 in
  
  // From table_spec_well_formed, all entries are < table_size
  assert (forall i. i `Set.mem` entries ==> i < table_size);
  // So table_size is not in entries
  assert (not (table_size `Set.mem` entries));
  
  // Prove forall i. i >= new_table_size \/ not (i `Set.mem` new_entries) ==> new_spec i == 0.0R
  assert (forall i. i >= new_table_size ==> i <> table_size);
  assert (forall i. i >= new_table_size ==> new_spec i == spec i);
  
  // Prove forall i. i `Set.mem` new_entries ==> i < new_table_size
  // new_entries = {table_size} ∪ entries
  // For table_size: table_size < new_table_size = table_size + 1 ✓
  // For i in entries: i < table_size < new_table_size ✓
  
  // total_frac new_spec entries == total_frac spec entries
  // since new_spec i == spec i for all i in entries (entries all < table_size)
  assert (forall i. i `Set.mem` entries ==> new_spec i == spec i);
  total_frac_extensional new_spec spec entries;
  
  // Prove total_frac new_spec new_entries + half_f == 1.0R
  total_frac_insert_fresh new_spec entries table_size;
  // total_frac new_spec new_entries = new_spec table_size + total_frac new_spec entries
  //                                 = half_f + total_frac spec entries
  assert (total_frac new_spec new_entries == half_f +. total_frac spec entries);
  //                                    = half_f + (1.0R - f)
  assert (total_frac spec entries == 1.0R -. f);
  //                                    = half_f + 1.0R - 2*half_f
  assert (f == 2.0R *. half_f);
  //                                    = 1.0R - half_f
  assert (total_frac new_spec new_entries == 1.0R -. half_f);
  // total_frac new_spec new_entries <. 1.0R (since half_f >. 0.0R)
  ()

/// Helper lemma: removing an entry from total_frac
let total_frac_remove (tab:table_spec) (entries:index_set) (i:nat)
: Lemma 
  (requires i `Set.mem` entries)
  (ensures total_frac tab entries == tab i +. total_frac tab (remove_element i entries))
= total_frac_sum tab i entries

/// Helper lemma: table_spec_well_formed for shrunk spec (release reader)
let table_spec_well_formed_shrink (spec:table_spec) (table_size:nat) (entries:index_set) 
                                   (avail:perm) (reader_pos:nat) (f:perm)
: Lemma 
  (requires 
    table_spec_well_formed spec table_size entries /\
    total_frac spec entries +. avail == 1.0R /\
    reader_pos `Set.mem` entries /\
    reader_pos < table_size /\
    spec reader_pos == f /\
    f >. 0.0R)
  (ensures
    (let new_spec : table_spec = (fun i -> if i = reader_pos then 0.0R else spec i) in
     let new_entries = Set.remove reader_pos entries in
     let new_avail = avail +. f in
     table_spec_well_formed new_spec table_size new_entries /\
     total_frac new_spec new_entries +. new_avail == 1.0R))
= Set.all_finite_set_facts_lemma ();
  let new_spec : table_spec = (fun i -> if i = reader_pos then 0.0R else spec i) in
  let new_entries = Set.remove reader_pos entries in
  let new_avail = avail +. f in
  
  // Prove forall i. i >= table_size \/ not (i `Set.mem` new_entries) ==> new_spec i == 0.0R
  // Case 1: i >= table_size => spec i == 0.0R (from table_spec_well_formed spec) => new_spec i = 0.0R if i <> reader_pos, = 0.0R if i = reader_pos
  // Case 2: not (i `Set.mem` new_entries) and i <> reader_pos => not (i `Set.mem` entries) => spec i = 0.0R => new_spec i = 0.0R
  // Case 2': not (i `Set.mem` new_entries) and i = reader_pos => new_spec i = 0.0R by definition
  assert (forall i. i `Set.mem` new_entries ==> i `Set.mem` entries);
  assert (forall i. i `Set.mem` new_entries ==> i < table_size);
  
  // Prove total_frac new_spec new_entries + new_avail == 1.0R
  // new_spec i = spec i for i <> reader_pos
  // So total_frac new_spec new_entries = total_frac spec new_entries (since reader_pos not in new_entries)
  assert (forall i. i `Set.mem` new_entries ==> new_spec i == spec i);
  total_frac_extensional new_spec spec new_entries;
  
  // total_frac spec entries = spec reader_pos + total_frac spec new_entries
  total_frac_remove spec entries reader_pos;
  // So total_frac spec new_entries = total_frac spec entries - f
  //                                = (1.0R - avail) - f
  //                                = 1.0R - avail - f
  //                                = 1.0R - (avail + f)
  //                                = 1.0R - new_avail
  // Thus total_frac new_spec new_entries + new_avail = (1.0R - new_avail) + new_avail = 1.0R
  assert (total_frac new_spec new_entries == total_frac spec new_entries);
  assert (total_frac spec entries == f +. total_frac spec new_entries);
  assert (total_frac spec entries == 1.0R -. avail);
  assert (total_frac spec new_entries == 1.0R -. avail -. f);
  assert (new_avail == avail +. f);
  assert (total_frac new_spec new_entries +. new_avail == 1.0R);
  ()

let owns_half_table_entry (perm_table:GFT.table frac) (spec:table_spec) (index:nat) : slprop =
  GFT.pts_to perm_table index #0.5R (spec index)

/// Helper: if two specs agree on range [0, n), the on_range predicates are equal
let owns_half_entry_spec_agree (perm_table:GFT.table frac) (spec1 spec2:table_spec) (i:nat)
  : Lemma (requires spec1 i == spec2 i)
          (ensures owns_half_table_entry perm_table spec1 i == owns_half_table_entry perm_table spec2 i)
  = ()

/// Helper lemma: if spec i > 0 and i < size and table_spec_well_formed, then i is in entries
let nonzero_spec_in_entries (spec:table_spec) (size:nat) (entries:index_set) (i:nat)
  : Lemma (requires table_spec_well_formed spec size entries /\ i < size /\ spec i >. 0.0R)
          (ensures i `Set.mem` entries)
  = // Contrapositive of: not (i in entries) ==> spec i = 0
    // table_spec_well_formed says: i >= size \/ not (i in entries) ==> spec i = 0
    // Since i < size, if not (i in entries), then spec i = 0
    // But spec i > 0, so i must be in entries
    ()

/// Helper lemma: if there's an element in entries, then cardinality > 0
let nonempty_has_positive_cardinality (entries:index_set) (i:nat)
  : Lemma (requires i `Set.mem` entries)
          (ensures Set.cardinality entries > 0)
  = Set.all_finite_set_facts_lemma ()

/// Helper lemma: counter bounds when there's a reader
let counter_bounds_with_reader (n:U32.t) (size:nat) (entries:index_set) (spec:table_spec) (avail:perm) (i:nat)
  : Lemma (requires 
            (if n = writer_sentinel then Set.cardinality entries = 0 else Set.cardinality entries == U32.v n) /\
            table_spec_well_formed spec size entries /\
            i < size /\
            spec i >. 0.0R)
          (ensures U32.v n > 0 /\ n <> writer_sentinel)
  = nonzero_spec_in_entries spec size entries i;
    nonempty_has_positive_cardinality entries i;
    // Now Set.cardinality entries > 0
    // If n = writer_sentinel, then cardinality = 0, contradiction
    // If n = 0, then cardinality = 0, contradiction
    // Therefore n > 0 and n <> writer_sentinel
    ()

// Explicit pure predicate for table_relation
// We'll have to fold and unfold this in proofs
// Useful to guide instantiations of existstials in rwlock_inv_aux
let table_relation (n : U32.t) (table_size : nat) (entries:index_set) (spec:table_spec) (f:perm) =
  pure (
    (if n = writer_sentinel 
     then Set.cardinality entries = 0  //if the writer holds, then there are no active readers
     else Set.cardinality entries == U32.v n) /\ //otherwise, number of active readers = n
    table_spec_well_formed spec table_size entries /\ //the 
    total_frac spec entries +. f == 1.0R
  )

let ghost_counter_perm (n:U32.t) : perm =
  if n = writer_sentinel then 0.5R else 1.0R

let rwlock_inv_aux (pred : perm -> slprop)
                   (counter : B.box U32.t)
                   (ghost_counter: GR.ref U32.t)
                   (perm_table : GFT.table frac)
: slprop
= exists* (n : U32.t) (table_size : nat) (entries:index_set) (spec:table_spec) (f:perm). 
    B.pts_to counter n ** //counter is the actual physical counter on which do atomic operations
    GR.pts_to ghost_counter #(ghost_counter_perm n) n ** //ghost witness of counter value, only half when writer locks
    GFT.is_table perm_table table_size ** //permission to the table itself, allcoated up to table_size
    OR.on_range (owns_half_table_entry perm_table spec) 0 table_size ** //half permission to all the table entries up to table size
    (if n = writer_sentinel then emp else pred f) ** //available permission in the lock
    table_relation n table_size entries spec f ///pure relation tying it all together

let rwlock_inv (pred : perm -> slprop)
               (counter : B.box U32.t)
               (ghost_counter: GR.ref U32.t)
               (perm_table : GFT.table frac)
: slprop
= rwlock_inv_aux pred counter ghost_counter perm_table

//
// Lock type
//

noeq
type rwlock_rec (pred : perm -> slprop) = {
  counter : B.box U32.t;
  ghost_counter: GR.ref U32.t;
  perm_table : GFT.table frac;
  cinv : cinv;
  frac_pred : squash (fractional pred);
}

let rwlock (pred : perm -> slprop) : Type0 = rwlock_rec pred

/// is_rwlock: own a share of the cancellable invariant
let is_rwlock #pred (l : rwlock pred) (#p:perm) : slprop =
  inv (iname_of l.cinv) (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table)) **
  active l.cinv p

//
// Reader and writer tokens
//

/// Reader parts: the permission data for a reader token
let reader_parts #pred (l : rwlock pred) (f:frac) : slprop = 
  exists* (i : nat).
    GFT.pts_to l.perm_table i #0.5R f ** //entry i in the table has a non-zero fraction
    pure (f >. 0.0R) 
    //so, the cardinality of the set of active entries is at least 1
    //and so the counter must be at least 1

/// Reader token: owns 0.5R of the table entry at position i
/// This is the reader's proof that they have acquired the lock
let reader_token #pred (l : rwlock pred) (f:perm) = 
  reader_parts l f ** pred f

/// Writer token: ghost witness that writer has the lock  
let writer_token (#pred : perm -> slprop) (l : rwlock pred) : slprop =
  GR.pts_to l.ghost_counter #0.5R writer_sentinel

//
// Create
//

fn create (#pred : perm -> slprop) (frac_pred : squash (fractional pred))
  requires pred 1.0R
  returns l : rwlock pred
  ensures is_rwlock l #1.0R
{
  // Allocate the physical counter initialized to 0
  let counter = B.alloc 0ul;
  
  // Allocate ghost state for the counter
  let ghost_counter = GR.alloc #U32.t 0ul;
  
  // Create empty permission table
  let perm_table = GFT.create #frac;
  
  // Initial state: 
  // - n = 0 (no readers, no writer)
  // - table_size = 0
  // - entries = empty set
  // - spec = all zeros
  // - f = 1.0R (all permission available)
  let empty_spec : table_spec = (fun _ -> 0.0R);
  let empty_entries : index_set = Set.emptyset;
  
  // Create the invariant
  OR.on_range_empty (owns_half_table_entry perm_table empty_spec) 0;
  
  // Show ghost_counter_perm 0ul = 1.0R
  assert (pure (ghost_counter_perm 0ul == 1.0R));
  rewrite (GR.pts_to ghost_counter #1.0R 0ul) 
       as (GR.pts_to ghost_counter #(ghost_counter_perm 0ul) 0ul);
  
  // Prove table_relation
  Set.all_finite_set_facts_lemma ();
  assert (pure (Set.cardinality empty_entries == 0));
  assert (pure (total_frac empty_spec empty_entries == 0.0R));
  fold (table_relation 0ul 0 empty_entries empty_spec 1.0R);
  
  // Fold the invariant
  rewrite (pred 1.0R) as (if 0ul = writer_sentinel then emp else pred 1.0R);
  fold (rwlock_inv_aux pred counter ghost_counter perm_table);
  fold (rwlock_inv pred counter ghost_counter perm_table);
  
  // Create cancellable invariant
  let cinv = CInv.new_cancellable_invariant (rwlock_inv pred counter ghost_counter perm_table);
  
  // Build the lock
  let l : rwlock pred = {
    counter = counter;
    ghost_counter = ghost_counter;
    perm_table = perm_table;
    cinv = cinv;
    frac_pred = frac_pred;
  };
  
  // Rewrite to use record field names
  rewrite (inv (iname_of cinv) (cinv_vp cinv (rwlock_inv pred counter ghost_counter perm_table)))
       as (inv (iname_of l.cinv) (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table)));
  rewrite (active cinv 1.0R) as (active l.cinv 1.0R);
  
  // Fold is_rwlock
  fold (is_rwlock l #1.0R);
  l
}

//
// Reader acquire
//

/// Helper to weaken a single entry when specs agree (used with on_range_weaken)
/// Note: we don't need the pure constraint if we know specs agree pointwise
ghost
fn weaken_single_entry 
    (perm_table: GFT.table frac)
    (spec1 spec2: table_spec)
    (i j: nat)
    (pf: squash (forall (k:nat). i <= k /\ k < j ==> spec1 k == spec2 k))
    (k: nat{i <= k /\ k < j})
  requires owns_half_table_entry perm_table spec1 k
  ensures owns_half_table_entry perm_table spec2 k
{
  unfold (owns_half_table_entry perm_table spec1 k);
  // Now we have GFT.pts_to perm_table k #0.5R (spec1 k)
  // Since spec1 k == spec2 k (from pf), we can fold to spec2
  fold (owns_half_table_entry perm_table spec2 k)
}

/// Try to acquire reader: CAS counter from expected to expected+1
fn try_acquire_reader_at (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred) 
                         (expected : (n:U32.t{U32.v n <= U32.v max_readers}))
  preserves is_rwlock l #perm_lock
  returns result : option perm
  ensures (match result with Some f -> reader_token l f | None -> emp)
{
  unfold (is_rwlock l #perm_lock);
  let new_count : U32.t = U32.add expected 1ul;
  let expected:U32.t = expected;
  // Compute the fact outside with_invariants so it's in scope
  expected_not_sentinel expected;
  
  let result : (bool & perm) =
    with_invariants (bool & perm) emp_inames (CInv.iname_of l.cinv)
        (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table))
        (active l.cinv perm_lock ** pure ((expected <: U32.t) <> writer_sentinel))
        (fun r -> active l.cinv perm_lock ** cond (fst r) (reader_parts l (snd r) ** pred (snd r)) emp)
    fn _ {
      unpack_cinv_vp l.cinv;
      unfold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      unfold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      
      with n table_size entries spec f. _;
      unfold (table_relation n table_size entries spec f);
      
      // Try CAS from expected to expected+1
      let b = cas_box l.counter expected new_count;
      
      if b {
        elim_cond_true _ _ _;
        // CAS succeeded! n was expected, now new_count
        rewrite each n as expected;
        
        // Update ghost_counter to match the new physical counter value
        // ghost_counter_perm expected = 1.0R since expected <> writer_sentinel
        // ghost_counter_perm new_count = 1.0R since new_count <= max_readers + 1 < writer_sentinel
        rewrite (GR.pts_to l.ghost_counter #(ghost_counter_perm expected) expected)
             as (GR.pts_to l.ghost_counter #1.0R expected);
        GR.write l.ghost_counter new_count;
        rewrite (GR.pts_to l.ghost_counter #1.0R new_count)
             as (GR.pts_to l.ghost_counter #(ghost_counter_perm new_count) new_count);
        
        // Since expected <> writer_sentinel (from precondition), we have pred f
        rewrite (if expected = writer_sentinel then emp else pred f) as (pred f);
        
        // Split: pred f == pred (f/2) ** pred (f/2)
        let half_f : perm = f /. 2.0R;
        half_plus_half f;
        fractional_split_lemma pred half_f half_f;
        rewrite (pred f) as (pred half_f ** pred half_f);
        
        // Allocate new table entry with value half_f at position table_size
        GFT.alloc l.perm_table half_f;
        
        // Split the new entry: 0.5R for invariant, 0.5R for reader
        GFT.share l.perm_table table_size 0.5R 0.5R;
        
        // Prove table_spec_well_formed and total_frac properties for new state
        // We'll use (table_size + 1) as new_table_size and Set.insert table_size entries as new_entries
        // and (fun i -> if i = table_size then half_f else spec i) as new_spec
        Set.all_finite_set_facts_lemma ();
        table_spec_well_formed_extend spec table_size entries f half_f;
        
        assert (pure (Set.cardinality (Set.insert table_size entries) == Set.cardinality entries + 1));
        assert (pure (Set.cardinality (Set.insert table_size entries) == U32.v expected + 1));
        assert (pure (Set.cardinality (Set.insert table_size entries) == U32.v new_count));
        assert (pure (half_f >. 0.0R));
        
        // Rewrite the invariant's half entry  
        // new_spec = (fun i -> if i = table_size then half_f else spec i)
        // For table_size, new_spec table_size = half_f
        rewrite (GFT.pts_to l.perm_table table_size #0.5R half_f)
             as (owns_half_table_entry l.perm_table (fun i -> if i = table_size then half_f else spec i) table_size);
        
        // Extend on_range: for k < table_size, new_spec k = spec k
        // Use on_range_weaken with a rewrite at each position
        OR.on_range_weaken
          (owns_half_table_entry l.perm_table spec)
          (owns_half_table_entry l.perm_table (fun i -> if i = table_size then half_f else spec i))
          0 table_size
          (weaken_single_entry l.perm_table spec (fun i -> if i = table_size then half_f else spec i) 0 table_size ());
        OR.on_range_snoc ();
        
        // GFT.is_table should already be at table_size + 1 after alloc
        // Fold table_relation for new state
        fold (table_relation new_count (table_size + 1) (Set.insert table_size entries) 
                             (fun i -> if i = table_size then half_f else spec i) half_f);
        
        // Fold the predicate part
        rewrite (pred half_f) as (if new_count = writer_sentinel then emp else pred half_f);
        
        // Fold the invariant
        fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
        fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
        pack_cinv_vp l.cinv;
        
        // Prepare reader parts
        fold (reader_parts l half_f);
        
        rewrite (reader_parts l half_f ** pred half_f)
             as (cond true (reader_parts l half_f ** pred half_f) emp);
        (true, half_f)
      } else {
        elim_cond_false _ _ _;
        // CAS failed - refold invariant
        fold (table_relation n table_size entries spec f);
        fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
        fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
        pack_cinv_vp l.cinv;
        // Need to fold the cond false into emp
        intro_cond_false (reader_parts l f ** pred f) emp;
        (false, f)
      }
    };
  
  fold (is_rwlock l #perm_lock);
  
  let (success, f) = result;
  if success {
    elim_cond_true success _ _;
    fold (reader_token l f);
    Some f
  } else {
    elim_cond_false success _ _;
    None #perm
  }
}

/// Read the current counter value
fn read_counter (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  returns n : U32.t
  ensures emp
{
  unfold (is_rwlock l #perm_lock);
  
  let result =
    with_invariants U32.t emp_inames (CInv.iname_of l.cinv)
        (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table))
        (active l.cinv perm_lock)
        (fun _ -> active l.cinv perm_lock)
    fn _ {
      unpack_cinv_vp l.cinv;
      unfold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      unfold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      
      with n table_size entries spec f. _;
      
      let v = read_atomic_box l.counter;
      
      fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      pack_cinv_vp l.cinv;
      v
    };
  
  fold (is_rwlock l #perm_lock);
  result
}

/// Read the current counter value while holding a reader token
/// Proves that the counter is > 0 and < writer_sentinel
fn read_counter_for_release (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred) (#f:perm)
  requires is_rwlock l #perm_lock ** reader_token l f
  returns n : (v:U32.t{U32.v v > 0 /\ U32.v v < U32.v writer_sentinel})
  ensures is_rwlock l #perm_lock ** reader_token l f
{
  unfold (is_rwlock l #perm_lock);
  unfold (reader_token l f);
  unfold (reader_parts l f);
  
  with reader_pos. _;
  
  let result =
    with_invariants (v:U32.t{U32.v v > 0 /\ U32.v v < U32.v writer_sentinel}) emp_inames (CInv.iname_of l.cinv)
        (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table))
        (active l.cinv perm_lock ** GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R))
        (fun _ -> active l.cinv perm_lock ** GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R))
    fn _ {
      unpack_cinv_vp l.cinv;
      unfold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      unfold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      
      with n table_size entries spec avail. _;
      unfold (table_relation n table_size entries spec avail);
      
      // Read the counter
      let v = read_atomic_box l.counter;
      
      // Prove v > 0 and v < writer_sentinel using the reader token
      GFT.in_bounds l.perm_table;
      // reader_pos < table_size
      
      // Get entry from on_range
      OR.on_range_get reader_pos;
      rewrite (owns_half_table_entry l.perm_table spec reader_pos)
           as (GFT.pts_to l.perm_table reader_pos #0.5R (spec reader_pos));
      
      // Gather to show spec reader_pos = f
      GFT.gather #frac l.perm_table reader_pos #0.5R #0.5R #(spec reader_pos) #f;
      // Now we have pure (spec reader_pos == f) and f > 0
      // So spec reader_pos > 0
      
      // Use the helper lemma to prove counter bounds
      // We need: table_spec_well_formed spec table_size entries /\ reader_pos < table_size /\ spec reader_pos > 0
      // From table_relation: n = 0 or n = sentinel ==> cardinality = 0; else cardinality = n
      // And table_spec_well_formed
      counter_bounds_with_reader n table_size entries spec avail reader_pos;
      // Now we have: U32.v n > 0 /\ n <> writer_sentinel
      // Since v = n (from read_atomic_box), U32.v v > 0 /\ v <> writer_sentinel
      assert (pure (U32.v v > 0 /\ U32.v v < U32.v writer_sentinel));
      
      // Split back for the invariant
      GFT.share l.perm_table reader_pos 0.5R 0.5R;
      
      // Put entry back into on_range
      rewrite (GFT.pts_to l.perm_table reader_pos #0.5R (spec reader_pos))
           as (owns_half_table_entry l.perm_table spec reader_pos);
      OR.on_range_put 0 reader_pos table_size;
      
      // Refold invariant
      fold (table_relation n table_size entries spec avail);
      fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      pack_cinv_vp l.cinv;
      v
    };
  
  fold (reader_parts l f);
  fold (reader_token l f);
  fold (is_rwlock l #perm_lock);
  result
}

/// Acquire reader: spin until successful
/// Reads current counter and tries to increment (if not at max or writer-held)
fn rec acquire_reader (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  returns f : perm
  ensures reader_parts l f ** pred f
{
  // Read current counter value through the invariant
  let current = read_counter l;
  
  // Check if we can try to acquire (not writer-held, not at max)
  // writer_sentinel = 0xFFFFFFFF, max_readers = 0xFFFFFFFE
  let is_writer_held = (current = writer_sentinel);
  let at_max = U32.gte current max_readers;
  if is_writer_held {
    // Writer holds the lock, retry
    acquire_reader l
  } else {
    if at_max {
      // At max readers, retry
      acquire_reader l
    } else {
      // Try to CAS from current to current+1
      let result = try_acquire_reader_at l current;
      match result {
        Some f -> { 
          unfold (reader_token l f);
          f 
        }
        None -> { acquire_reader l }
      }
    }
  }
}

//
// Reader release
//

/// Try to release reader with expected count
fn try_release_reader_at (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred) (#f:perm)
                         (expected : (n:U32.t{U32.v n > 0 /\ U32.v n < U32.v writer_sentinel}))
  requires is_rwlock l #perm_lock ** reader_token l f
  returns b : bool
  ensures is_rwlock l #perm_lock ** cond b emp (reader_token l f)
{
  unfold (is_rwlock l #perm_lock);
  unfold (reader_token l f);
  unfold (reader_parts l f);
  
  // Get the reader's table entry position
  with reader_pos. _;
  
  // Compute new value outside atomic block
  let new_count : U32.t = U32.sub expected 1ul;
  
  // Prove expected <> writer_sentinel outside with_invariants
  let expected:U32.t = expected;
  release_expected_not_sentinel expected;
  
  // Try to CAS decrement the counter
  let result =
    with_invariants bool emp_inames (CInv.iname_of l.cinv)
        (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table))
        (active l.cinv perm_lock ** GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R) ** pure (expected <> writer_sentinel))
        (fun b -> active l.cinv perm_lock ** cond b emp (GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R)))
    fn _ {
      unpack_cinv_vp l.cinv;
      unfold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      unfold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      
      with n table_size entries spec avail. _;
      unfold (table_relation n table_size entries spec avail);
      
      // Try CAS from expected to new_count
      let cas_result = cas_box l.counter expected new_count;
      
      if cas_result {
        elim_cond_true _ _ _;
        // CAS succeeded! n was expected, now new_count
        rewrite each n as expected;
        
        // Update ghost_counter to match the new physical counter value
        // ghost_counter_perm expected = 1.0R since expected <> writer_sentinel
        // ghost_counter_perm new_count = 1.0R since new_count = expected - 1 > 0 (well, could be 0)
        rewrite (GR.pts_to l.ghost_counter #(ghost_counter_perm expected) expected)
             as (GR.pts_to l.ghost_counter #1.0R expected);
        GR.write l.ghost_counter new_count;
        rewrite (GR.pts_to l.ghost_counter #1.0R new_count)
             as (GR.pts_to l.ghost_counter #(ghost_counter_perm new_count) new_count);
        
        // Since expected <> writer_sentinel (from precondition), we have pred avail
        rewrite (if expected = writer_sentinel then emp else pred avail) as (pred avail);
        
        // Get in_bounds to prove reader_pos < table_size
        GFT.in_bounds l.perm_table;
        assert (pure (reader_pos < table_size));
        
        // Get the invariant's half of the entry from on_range
        OR.on_range_get reader_pos;
        rewrite (owns_half_table_entry l.perm_table spec reader_pos)
             as (GFT.pts_to l.perm_table reader_pos #0.5R (spec reader_pos));
        
        // Gather: combine the two halves
        GFT.gather #frac l.perm_table reader_pos #0.5R #0.5R #(spec reader_pos) #f;
        // Now we have full permission on the entry, and spec reader_pos == f
        
        // Combine predicates: we have pred f from reader, pred avail from invariant
        fractional_combine_lemma pred avail f;
        rewrite (pred avail ** pred f) as (pred (avail +. f));
        
        // Inline definitions for new_entries, new_avail, new_spec
        // new_entries = Set.remove reader_pos entries
        // new_avail = avail +. f
        // new_spec = (fun i -> if i = reader_pos then 0.0R else spec i)
        
        // Update the table entry value to 0.0R so it matches new_spec
        GFT.update l.perm_table 0.0R;
        
        // Prove new table_relation using helper lemma
        Set.all_finite_set_facts_lemma ();
        // spec reader_pos == f follows from the gather (pure (p == q) gives us spec reader_pos == f)
        table_spec_well_formed_shrink spec table_size entries avail reader_pos f;
        
        // new_count <> writer_sentinel follows from expected > 0 and expected < writer_sentinel
        sub_preserves_not_sentinel expected;
        
        // Cardinality check: new_count = expected - 1, new_entries = entries - reader_pos
        // entries has expected elements, so new_entries has expected - 1 = new_count elements
        assert (pure (Set.cardinality (Set.remove reader_pos entries) == Set.cardinality entries - 1));
        assert (pure (Set.cardinality entries == U32.v expected));
        assert (pure (Set.cardinality (Set.remove reader_pos entries) == U32.v new_count));
        
        // Split the entry again for the invariant (value is now 0.0R)
        GFT.share l.perm_table reader_pos 0.5R 0.5R;
        
        // One half goes back to on_range
        // new_spec reader_pos = 0.0R, so owns_half_table_entry new_spec reader_pos = GFT.pts_to ... 0.0R
        rewrite (GFT.pts_to l.perm_table reader_pos #0.5R 0.0R)
             as (owns_half_table_entry l.perm_table (fun i -> if i = reader_pos then 0.0R else spec i) reader_pos);
        
        // Weaken the on_range parts from spec to new_spec
        // For indices != reader_pos, new_spec i = spec i
        OR.on_range_weaken
          (owns_half_table_entry l.perm_table spec)
          (owns_half_table_entry l.perm_table (fun i -> if i = reader_pos then 0.0R else spec i))
          0 reader_pos
          (weaken_single_entry l.perm_table spec (fun i -> if i = reader_pos then 0.0R else spec i) 0 reader_pos ());
        OR.on_range_weaken
          (owns_half_table_entry l.perm_table spec)
          (owns_half_table_entry l.perm_table (fun i -> if i = reader_pos then 0.0R else spec i))
          (reader_pos + 1) table_size
          (weaken_single_entry l.perm_table spec (fun i -> if i = reader_pos then 0.0R else spec i) (reader_pos + 1) table_size ());
        
        OR.on_range_put 0 reader_pos table_size;
        
        // Fold table_relation for new state
        fold (table_relation new_count table_size (Set.remove reader_pos entries) 
                             (fun i -> if i = reader_pos then 0.0R else spec i) (avail +. f));
        
        // Fold the predicate part
        rewrite (pred (avail +. f)) as (if new_count = writer_sentinel then emp else pred (avail +. f));
        
        // Fold the invariant
        fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
        fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
        pack_cinv_vp l.cinv;
        
        // Drop the leftover half (value is now 0.0R)
        drop_ (GFT.pts_to l.perm_table reader_pos #0.5R 0.0R);
        
        rewrite emp as (cond true emp (GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R)));
        true
      } else {
        elim_cond_false _ _ _;
        // CAS failed - refold invariant
        fold (table_relation n table_size entries spec avail);
        fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
        fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
        pack_cinv_vp l.cinv;
        rewrite (GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R))
             as (cond false emp (GFT.pts_to l.perm_table reader_pos #0.5R f ** pred f ** pure (f >. 0.0R)));
        false
      }
    };
  
  fold (is_rwlock l #perm_lock);
  
  if result {
    elim_cond_true result _ _;
    rewrite emp as (cond true emp (reader_token l f));
    true
  } else {
    elim_cond_false result _ _;
    fold (reader_parts l f);
    fold (reader_token l f);
    rewrite (reader_token l f) as (cond false emp (reader_token l f));
    false
  }
}

/// Release reader: spin until successful
/// Reads current counter and tries to decrement
fn rec release_reader (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred) (#f:perm)
  requires is_rwlock l #perm_lock ** reader_parts l f ** pred f
  ensures is_rwlock l #perm_lock
{
  // Fold reader_token for internal use
  fold (reader_token l f);
  
  // Read current counter value - proves counter is valid since we hold reader_token
  let current = read_counter_for_release l;
  
  // current is guaranteed to be > 0 and < writer_sentinel by read_counter_for_release
  // Try to CAS from current to current-1
  let success = try_release_reader_at l current;
  if success {
    elim_cond_true success _ _;
    ()
  } else {
    elim_cond_false success _ _;
    unfold (reader_token l f);
    release_reader l
  }
}

//
// Writer acquire
//

/// Acquire writer: CAS from 0 to sentinel
fn rec acquire_writer (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  preserves is_rwlock l #perm_lock
  ensures writer_token l ** pred 1.0R
{
  unfold (is_rwlock l #perm_lock);
  
  let result =
    with_invariants bool emp_inames (CInv.iname_of l.cinv)
        (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table))
        (active l.cinv perm_lock)
        (fun r -> active l.cinv perm_lock ** 
                  (if r then GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R else emp))
    fn _ {
      unpack_cinv_vp l.cinv;
      unfold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
      unfold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
      
      with n table_size entries spec f. _;
      unfold (table_relation n table_size entries spec f);
      
      // Try CAS from 0 to writer_sentinel
      let b = cas_box l.counter 0ul writer_sentinel;
      
      if b {
        elim_cond_true _ _ _;
        // CAS succeeded! n was 0, now writer_sentinel
        rewrite each n as 0ul;
        
        // n = 0 means no readers, so f = 1.0R
        Set.all_finite_set_facts_lemma ();
        assert (pure (Set.cardinality entries == 0));
        assert (pure (total_frac spec entries == 0.0R));
        assert (pure (f == 1.0R));
        
        // We have pred f = pred 1.0R
        rewrite (if 0ul = writer_sentinel then emp else pred f) as (pred 1.0R);
        
        // Split ghost_counter permission: 1.0R -> 0.5R + 0.5R
        // ghost_counter_perm 0ul = 1.0R
        rewrite (GR.pts_to l.ghost_counter #(ghost_counter_perm 0ul) 0ul)
             as (GR.pts_to l.ghost_counter #1.0R 0ul);
        GR.(l.ghost_counter := writer_sentinel);
        GR.share l.ghost_counter;
        
        // One half goes to writer token, one half stays in invariant
        // ghost_counter_perm writer_sentinel = 0.5R
        rewrite (GR.pts_to l.ghost_counter #0.5R writer_sentinel)
             as (GR.pts_to l.ghost_counter #(ghost_counter_perm writer_sentinel) writer_sentinel);
        
        // Fold table_relation for writer state
        fold (table_relation writer_sentinel table_size entries spec 1.0R);
        
        // Fold the predicate part (emp since writer_sentinel)
        rewrite emp as (if writer_sentinel = writer_sentinel then emp else pred 1.0R);
        
        // Fold the invariant
        fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
        fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
        pack_cinv_vp l.cinv;
        
        rewrite (GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R)
             as (if true then GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R else emp);
        true
      } else {
        elim_cond_false _ _ _;
        // CAS failed - refold invariant
        fold (table_relation n table_size entries spec f);
        fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
        fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
        pack_cinv_vp l.cinv;
        rewrite emp as (if false then GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R else emp);
        false
      }
    };
  
  fold (is_rwlock l #perm_lock);
  
  if result {
    rewrite (if result then GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R else emp)
         as (GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R);
    fold (writer_token l)
  } else {
    rewrite (if result then GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R else emp)
         as emp;
    acquire_writer l
  }
}

//
// Writer release
//

/// Release writer: set counter back to 0
fn release_writer (#pred : perm -> slprop) (#perm_lock:perm) (l : rwlock pred)
  requires is_rwlock l #perm_lock ** writer_token l ** pred 1.0R
  ensures is_rwlock l #perm_lock
{
  unfold (is_rwlock l #perm_lock);
  unfold (writer_token l);
  
  with_invariants unit emp_inames (CInv.iname_of l.cinv)
      (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table))
      (active l.cinv perm_lock ** GR.pts_to l.ghost_counter #0.5R writer_sentinel ** pred 1.0R)
      (fun _ -> active l.cinv perm_lock)
  fn _ {
    unpack_cinv_vp l.cinv;
    unfold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
    unfold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
    
    with n table_size entries spec f. _;
    unfold (table_relation n table_size entries spec f);
    
    // n should be writer_sentinel (since we have writer token)
    // Use ghost_counter to prove n = writer_sentinel
    GR.pts_to_injective_eq l.ghost_counter;
    rewrite each n as writer_sentinel;
    
    // Gather ghost_counter: 0.5R + 0.5R = 1.0R
    GR.gather l.ghost_counter;
    
    // Write counter back to 0
    write_atomic_box l.counter 0ul;
    GR.(l.ghost_counter := 0ul);
    
    // ghost_counter_perm 0ul = 1.0R
    rewrite (GR.pts_to l.ghost_counter #1.0R 0ul)
         as (GR.pts_to l.ghost_counter #(ghost_counter_perm 0ul) 0ul);
    
    // f = 1.0R when writer held
    rewrite (if writer_sentinel = writer_sentinel then emp else pred f) as emp;
    
    // Fold table_relation for unlocked state
    fold (table_relation 0ul table_size entries spec 1.0R);
    
    // Fold the predicate part
    rewrite (pred 1.0R) as (if 0ul = writer_sentinel then emp else pred 1.0R);
    
    // Fold the invariant
    fold (rwlock_inv_aux pred l.counter l.ghost_counter l.perm_table);
    fold (rwlock_inv pred l.counter l.ghost_counter l.perm_table);
    pack_cinv_vp l.cinv;
    
    ()
  };
  
  fold (is_rwlock l #perm_lock)
}

//
// Share/gather for is_rwlock
//

ghost
fn share (#pred:perm -> slprop) (#p:perm) (l:rwlock pred)
  requires is_rwlock l #p
  ensures is_rwlock l #(p /. 2.0R) ** is_rwlock l #(p /. 2.0R)
{
  unfold (is_rwlock l #p);
  CInv.share l.cinv;
  dup_inv (CInv.iname_of l.cinv) (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table));
  fold (is_rwlock l #(p /. 2.0R));
  fold (is_rwlock l #(p /. 2.0R))
}

ghost
fn gather (#pred:perm -> slprop) (#p1 #p2:perm) (l:rwlock pred)
  requires is_rwlock l #p1 ** is_rwlock l #p2
  ensures is_rwlock l #(p1 +. p2)
{
  unfold (is_rwlock l #p1);
  unfold (is_rwlock l #p2);
  CInv.gather l.cinv;
  drop_ (inv (iname_of l.cinv) (cinv_vp l.cinv (rwlock_inv pred l.counter l.ghost_counter l.perm_table)));
  fold (is_rwlock l #(p1 +. p2))
}
