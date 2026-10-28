module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model

(**
Finite mathematical sets and their sorted linked-list representation.

The abstract set is a characteristic sequence, NOT the runtime representation.
Keys are 1..capacity; 0 and capacity+1 are the two list sentinels. Nodes are
preallocated and reusable. This bounded universe is the main difference from
the dynamically allocated integer set in Jacobs and Piessens, POPL 2011,
Section 8. No history, prophecy, or insertion-count bound is needed.

The lemmas below identify exactly the two shadow links changed by insertion
or removal. A lock holder owns half of its shadow link, so unrelated operations
cannot change its outgoing edge while traversing hand over hand.
*)

module S = FStar.Seq

(** Membership is false for the sentinels and for keys outside the universe. *)
let member (s:S.seq bool) (k:nat) : bool =
  if 0 < k && k <= S.length s then S.index s (k - 1) else false

(** The positive sentinel is not a member of the abstract set. *)
let limit (s:S.seq bool) = S.length s + 1
let live (s:S.seq bool) (k:nat) = k == 0 \/ member s k

(** Find the first member at or after start, or the positive sentinel. *)
let rec scan (s:S.seq bool) (start:nat { start <= limit s })
  : Tot nat (decreases (limit s - start)) =
  if start = limit s then start
  else if member s start then start
  else scan s (start + 1)

(** Inactive nodes and the terminal sentinel have the canonical null link 0. *)
let shadow (s:S.seq bool) (k:nat) =
  if k = 0 || member s k then scan s (k + 1) else 0

(** Adjacent live nodes bound an interval containing no set members. *)
let gap (s:S.seq bool) (p c:nat) =
  live s p /\ p < c /\ c <= limit s /\
  (c == limit s \/ member s c) /\
  (forall (j:nat). p < j /\ j < c ==> not (member s j))

(** Bounds, membership, and minimality of the first successor search. *)
let rec scan_spec s (start:nat)
  : Lemma
      (requires start <= limit s)
      (ensures start <= scan s start /\ scan s start <= limit s /\
        (scan s start == limit s \/ member s (scan s start)) /\
        (forall (j:nat). start <= j /\ j < scan s start ==> not (member s j)))
      (decreases (limit s - start)) =
  if start < limit s && not (member s start) then scan_spec s (start + 1)

(** Nonzero shadows characterize live nodes and identify adjacent list nodes. *)
let shadow_spec s (k:nat)
  : Lemma
      (requires k <= limit s)
      (ensures (shadow s k =!= 0 <==> live s k) /\
        (live s k ==> gap s k (shadow s k))) =
  if live s k then scan_spec s (k + 1)

(** A candidate with the search's minimality property is its unique result. *)
let rec scan_unique s (start c:nat)
  : Lemma
      (requires start <= c /\ c <= limit s /\
        (c == limit s \/ member s c) /\
        (forall (j:nat). start <= j /\ j < c ==> not (member s j)))
      (ensures scan s start == c)
      (decreases (c - start)) =
  if start < c then scan_unique s (start + 1) c

(** Convert a relational adjacency proof back into the canonical shadow. *)
let gap_shadow s (p c:nat)
  : Lemma (requires gap s p c) (ensures shadow s p == c) =
  scan_unique s (p + 1) c

(** Two overlapping gaps have the same predecessor. *)
let gap_overlap s (p c j d k:nat)
  : Lemma
      (requires gap s p c /\ gap s j d /\ p < k /\ k <= c /\ j < k /\ k <= d)
      (ensures p == j) =
  if p < j then (
    assert (p < j /\ j < c);
    assert (not (member s j))
  ) else if j < p then (
    assert (j < p /\ p < d);
    assert (not (member s p))
  )

(** Single-key set update; all other memberships are preserved. *)
let change (s:S.seq bool) (k:nat { 0 < k /\ k < limit s }) (b:bool) =
  S.upd s (k - 1) b

let change_member s (k:nat) b (j:nat)
  : Lemma
      (requires 0 < k /\ k < limit s)
      (ensures member (change s k b) j == (if j == k then b else member s j)) =
  ()

(** Idempotent updates justify duplicate adds and absent removals. *)
let change_same s (k:nat)
  : Lemma
      (requires 0 < k /\ k < limit s)
      (ensures change s k (member s k) == s) =
  S.lemma_eq_intro (change s k (member s k)) s

(** Inserting into a locked gap changes only predecessor and new-node links. *)
let insert_links s (p c k:nat)
  : Lemma
      (requires gap s p c /\ p < k /\ k < c)
      (ensures
        not (member s k) /\
        (forall (j:nat { j <= limit s }).
          shadow (change s k true) j ==
            (if j == p then k else if j == k then c else shadow s j))) =
  let t = change s k true in
  introduce forall (j:nat { j <= limit s }).
    shadow t j == (if j == p then k else if j == k then c else shadow s j)
  with (
    change_member s k true j;
    introduce forall (x:nat).
      member t x == (if x == k then true else member s x)
    with (change_member s k true x);
    if j == p then (
      assert (gap t p k);
      gap_shadow t p k
    ) else if j == k then (
      assert (gap t k c);
      gap_shadow t k c
    ) else if live s j then (
      shadow_spec s j;
      let d = shadow s j in
      if j < k && k < d then gap_overlap s p c j d k;
      assert (gap t j d);
      gap_shadow t j d
    )
  )

(** Removing a locked successor changes only predecessor and removed-node links. *)
let remove_links s (p k c:nat)
  : Lemma
      (requires gap s p k /\ k < limit s /\ gap s k c)
      (ensures
        member s k /\
        (forall (j:nat { j <= limit s }).
          shadow (change s k false) j ==
            (if j == p then c else if j == k then 0 else shadow s j))) =
  let t = change s k false in
  introduce forall (j:nat { j <= limit s }).
    shadow t j == (if j == p then c else if j == k then 0 else shadow s j)
  with (
    change_member s k false j;
    introduce forall (x:nat).
      member t x == (if x == k then false else member s x)
    with (change_member s k false x);
    if j == p then (
      assert (gap t p c);
      gap_shadow t p c
    ) else if j == k then ()
    else if live s j then (
      shadow_spec s j;
      let d = shadow s j in
      if d == k then gap_overlap s p k j d k;
      assert (gap t j d);
      gap_shadow t j d
    )
  )

(** The public transition distinguishes observations from changes. *)
type operation = | Add | Remove | Contains
let answer op s k =
  match op with
  | Add -> not (member s k)
  | Remove | Contains -> member s k
let after op s (k:nat { 0 < k /\ k < limit s }) =
  match op with
  | Add -> change s k true
  | Remove -> change s k false
  | Contains -> s

(** A fresh set is empty at every key, including out-of-range keys. *)
let empty (capacity:nat) = S.create capacity false
let empty_member capacity k : Lemma (not (member (empty capacity) k)) = ()
let empty_shadow (capacity:nat) (k:nat)
  : Lemma
      (requires k <= capacity + 1)
      (ensures shadow (empty capacity) k == (if k == 0 then capacity + 1 else 0)) =
  if k == 0 then gap_shadow (empty capacity) 0 (capacity + 1)

let empty_shadows (capacity:nat)
  : Lemma (forall (k:nat). k <= capacity + 1 ==>
      shadow (empty capacity) k == (if k == 0 then capacity + 1 else 0)) =
  introduce forall (k:nat). k <= capacity + 1 ==>
    shadow (empty capacity) k == (if k == 0 then capacity + 1 else 0)
  with (if k <= capacity + 1 then empty_shadow capacity k)
