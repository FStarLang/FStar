module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations
#lang-pulse

(**
Logically atomic add, remove, and contains on a lock-coupling linked list.

Traversal and lock acquisition occur before opening the client AU. A changing
operation writes the target and predecessor links while holding their locks,
then commits the shadow/model update before unlocking. A nonchanging operation
commits while its observed predecessor edge is still locked. These ghost
linearization points lie inside protected intervals: no new atomic-pointer
primitive or assumption that multiple physical writes are atomic is needed.
Both paths give an exact result and preserve all other memberships.

The implementation and client invariants are separate. The queue example's
generic Actions combinators open the AU, frame a single implementation step,
restore the lexical invariant, then execute the delayed AU commitment.
No invariant stays open over blocking lock acquisition or traversal.

Unlike the paper, insertion acquires a preallocated inactive node's lock and
removal releases it for reuse. All acquired node indices increase, preserving
the hand-over-hand order. The proof establishes partial correctness, not
fairness, termination, or a lock-freedom theorem.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module Lock = Pulse.Lib.SpinLock
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model
module N = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
module D = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module U = Pulse.Lib.LogicalAtomicity.Update

let opened q op k inner credits phi =
  A.opened emp_inames inner (alpha q) (update q op k inner credits phi)
    (beta q op k) (fun _ r -> phi r)
let closing q op k inner credits phi s =
  A.closing emp_inames inner (alpha q) (update q op k inner credits phi)
    (beta q op k) (fun _ r -> phi r) s

(** These operation/window combinations leave the abstract set unchanged. *)
let observation op k c =
  (op == H.Add /\ c == k) \/ (op == H.Remove /\ k < c) \/ op == H.Contains
let observed_answer op (k c:nat) =
  match op with | H.Add -> false | H.Remove | H.Contains -> c = k

atomic fn observe_opened (q:Q.set) (op:H.operation) (k:Q.key q)
  (p:nat { p < k }) (c:nat { k <= c /\ c <= Q.capacity q + 1 /\ observation op k c })
  (inner:inames) (credits:nat) (phi:bool -> slprop)
  opens [q.Q.name]
  requires opened q op k inner credits phi ** Q.is_set q ** later_credit 1 **
    N.held (N.at q.Q.cells p) c
  returns r:bool
  ensures U.fupd inner emp_inames (phi r) **
    (Q.is_set q ** N.held (N.at q.Q.cells p) c)
{
  unfold Q.is_set;
  dup_inv q.Q.name (Q.body q.Q.cells q.Q.model);
  let r = with_invariants_a bool emp_inames q.Q.name (Q.body q.Q.cells q.Q.model)
    (opened q op k inner credits phi ** N.held (N.at q.Q.cells p) c)
    (fun r -> U.fupd inner emp_inames (phi r) ** N.held (N.at q.Q.cells p) c) fn _ {
    unfold Q.body;
    with s. _;
    unfold opened;
    unfold A.opened;
    with xs. _;
    unfold alpha;
    unfold Q.model;
    G.pts_to_injective_eq q.Q.model;
    rewrite each s as xs;
    unfold N.held;
    N.agree q.Q.cells 0 (H.shadow xs) p c;
    H.shadow_spec xs p;
    let r = observed_answer op k c;
    H.change_same xs k;
    assert pure (H.after op xs k == xs /\ r == H.answer op xs k);
    fold Q.model q (H.after op xs k);
    fold beta q op k xs r;
    fold closing q op k inner credits phi xs;
    fold N.held (N.at q.Q.cells p) c;
    fold Q.body q.Q.cells q.Q.model;
    D.delay inner (closing q op k inner credits phi xs ** beta q op k xs r) (phi r)
      (fun _ -> A.commit emp_inames inner (alpha q) (update q op k inner credits phi)
        (beta q op k) (fun _ r -> phi r) xs r);
    r
  };
  fold Q.is_set q;
  r
}

(** Perform the observation with one credit for each invariant opening. *)
fn observe (q:Q.set) (op:H.operation) (k:Q.key q)
  (p:nat { p < k }) (c:nat { k <= c /\ c <= Q.capacity q + 1 /\ observation op k c })
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q ** N.held (N.at q.Q.cells p) c
  requires update q op k inner credits phi
  returns r:bool
  ensures phi r
{
  later_credit_buy credits;
  later_credit_buy 1;
  unfold update;
  slprop_equivs ();
  D.with_update inner (add_inv emp_inames q.Q.name) credits
    (alpha q) (beta q op k) (fun _ r -> phi r)
    (Q.is_set q ** later_credit 1 ** N.held (N.at q.Q.cells p) c)
    (Q.is_set q ** N.held (N.at q.Q.cells p) c) phi
    (fun _ -> observe_opened q op k p c inner credits phi)
}

let mode (insert:bool) = if insert then H.Add else H.Remove
let new_predecessor (insert:bool) (k old:nat) = if insert then k else old
let new_target (insert:bool) (c:nat) = if insert then c else 0

(** Both physical writes are complete, but both old shadows are still held.
Neither changed edge can be observed until the corresponding lock is released. *)
let prepared (q:Q.set) (insert:bool) (p:Q.node q) (k:Q.key q) (c old:nat) =
  N.access (N.at q.Q.cells p) ** Lock.lock_acquired (N.at q.Q.cells p).N.lock **
  B.pts_to (N.at q.Q.cells p).N.next (new_predecessor insert k old) **
  G.pts_to (N.at q.Q.cells p).N.shadow #0.5R c **
  N.access (N.at q.Q.cells k) ** Lock.lock_acquired (N.at q.Q.cells k).N.lock **
  B.pts_to (N.at q.Q.cells k).N.next (new_target insert c) **
  G.pts_to (N.at q.Q.cells k).N.shadow #0.5R old

atomic fn change_opened (q:Q.set) (insert:bool) (k:Q.key q)
  (p:nat { p < k })
  (c:nat { k <= c /\ c <= Q.capacity q + 1 /\ (if insert then k < c else k == c) })
  (old:nat) (inner:inames) (credits:nat) (phi:bool -> slprop)
  opens [q.Q.name]
  requires opened q (mode insert) k inner credits phi ** Q.is_set q ** later_credit 1 **
    prepared q insert p k c old
  returns r:bool
  ensures U.fupd inner emp_inames (phi r) ** (Q.is_set q **
    N.held (N.at q.Q.cells p) (new_predecessor insert k old) **
    N.held (N.at q.Q.cells k) (new_target insert c))
{
  unfold Q.is_set;
  dup_inv q.Q.name (Q.body q.Q.cells q.Q.model);
  let r = with_invariants_a bool emp_inames q.Q.name (Q.body q.Q.cells q.Q.model)
    (opened q (mode insert) k inner credits phi ** prepared q insert p k c old)
    (fun r -> U.fupd inner emp_inames (phi r) **
      N.held (N.at q.Q.cells p) (new_predecessor insert k old) **
      N.held (N.at q.Q.cells k) (new_target insert c)) fn _ {
    unfold Q.body;
    with s. _;
    unfold opened;
    unfold A.opened;
    with xs. _;
    unfold alpha;
    unfold Q.model;
    G.pts_to_injective_eq q.Q.model;
    rewrite each s as xs;
    unfold prepared;
    N.agree q.Q.cells 0 (H.shadow xs) p c;
    N.agree q.Q.cells 0 (H.shadow xs) k old;
    H.shadow_spec xs p;
    H.shadow_spec xs k;
    if insert { H.insert_links xs p c k; () }
    else { H.remove_links xs p k old; () };
    rewrite each (match insert with | true -> true | false -> false) as insert;
    N.set_shadow q.Q.cells 0 (H.shadow xs) p c (new_predecessor insert k old);
    N.set_shadow q.Q.cells 0
      (fun j -> if j == 0 + p then new_predecessor insert k old else H.shadow xs j)
      k old (new_target insert c);
    N.shadows_ext q.Q.cells 0
      (fun j -> if j == 0 + k then new_target insert c
        else if j == 0 + p then new_predecessor insert k old else H.shadow xs j)
      (H.shadow (H.after (mode insert) xs k));
    G.gather q.Q.model;
    G.write q.Q.model (H.after (mode insert) xs k);
    G.share q.Q.model;
    rewrite each (1.0R /. 2.0R) as 0.5R;
    fold Q.model q (H.after (mode insert) xs k);
    fold beta q (mode insert) k xs true;
    fold closing q (mode insert) k inner credits phi xs;
    fold N.held (N.at q.Q.cells p) (new_predecessor insert k old);
    fold N.held (N.at q.Q.cells k) (new_target insert c);
    fold Q.body q.Q.cells q.Q.model;
    D.delay inner
      (closing q (mode insert) k inner credits phi xs ** beta q (mode insert) k xs true)
      (phi true)
      (fun _ -> A.commit emp_inames inner (alpha q)
        (update q (mode insert) k inner credits phi) (beta q (mode insert) k)
        (fun _ r -> phi r) xs true);
    true
  };
  fold Q.is_set q;
  r
}

(** Finish a successful change after locating and locking its predecessor.
Preparing the target is not observable by another operation until publication. *)
divergent fn change (q:Q.set) (insert:bool) (k:Q.key q)
  (p:nat { p < k })
  (c:nat { k <= c /\ c <= Q.capacity q + 1 /\ (if insert then k < c else k == c) })
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q (mode insert) k inner credits phi ** N.held (N.at q.Q.cells p) c
  returns r:bool
  ensures phi r
{
  unfold Q.is_set;
  let old = N.acquire q.Q.cells k;
  unfold N.held (N.at q.Q.cells k) old;
  B.((N.at q.Q.cells k).N.next := new_target insert c);
  unfold N.held (N.at q.Q.cells p) c;
  B.((N.at q.Q.cells p).N.next := new_predecessor insert k old);
  fold prepared q insert p k c old;
  fold Q.is_set q;
  later_credit_buy credits;
  later_credit_buy 1;
  unfold update;
  slprop_equivs ();
  let r = D.with_update inner (add_inv emp_inames q.Q.name) credits
    (alpha q) (beta q (mode insert) k) (fun _ r -> phi r)
    (Q.is_set q ** later_credit 1 ** prepared q insert p k c old)
    (Q.is_set q ** N.held (N.at q.Q.cells p) (new_predecessor insert k old) **
      N.held (N.at q.Q.cells k) (new_target insert c)) phi
    (fun _ -> change_opened q insert k p c old inner credits phi);
  Q.unlock q k;
  Q.unlock q p;
  r
}

(** Add returns true iff k was absent at commitment, and installs k. *)
divergent fn add (q:Q.set) (k:Q.key q)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q H.Add k inner credits phi
  returns r:bool
  ensures phi r
{
  let w = Q.locate q k;
  let p, c = w;
  if (c = k) {
    let r = observe q H.Add k p c inner credits phi;
    Q.unlock q p;
    r
  } else {
    change q true k p c inner credits phi
  }
}

(** Remove returns true iff k was present, and clears only k's membership. *)
divergent fn remove (q:Q.set) (k:Q.key q)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q H.Remove k inner credits phi
  returns r:bool
  ensures phi r
{
  let w = Q.locate q k;
  let p, c = w;
  if (c = k) {
    change q false k p c inner credits phi
  } else {
    let r = observe q H.Remove k p c inner credits phi;
    Q.unlock q p;
    r
  }
}

(** Contains commits a read-only AU and leaves every membership unchanged. *)
divergent fn contains (q:Q.set) (k:Q.key q)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q H.Contains k inner credits phi
  returns r:bool
  ensures phi r
{
  let w = Q.locate q k;
  let p, c = w;
  let r = observe q H.Contains k p c inner credits phi;
  Q.unlock q p;
  r
}
