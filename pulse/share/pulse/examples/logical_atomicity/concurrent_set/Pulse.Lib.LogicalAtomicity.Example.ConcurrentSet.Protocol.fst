module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Protocol

(**
Pure client protocol for the POPL 2011 producer/consumer example.

A producer inserts 1,2,... once each. The consumer may choose any key.
The producer cursor p and the consumer's removed-set d partition the produced
prefix exactly: a key is in the shared set iff it has been produced but has
not been removed. Tracking all removed keys strengthens the paper's invariant,
which records only the last removed key.

These are CLIENT constraints, not restrictions on the set implementation:
ordinary set clients may remove and reinsert the same key arbitrarily.
*)

module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model

(** Exact partition of the produced prefix, plus no premature removals. *)
let consistent (s:S.seq bool) (p:nat) (d:S.seq bool) =
  S.length d == S.length s /\ p <= S.length s /\
  (forall (k:nat). H.member d k ==> k <= p) /\
  (forall (k:nat). H.member s k <==>
    0 < k /\ k <= p /\ not (H.member d k))

let prefix (n p:nat) =
  let count = if p < n then p else n in
  S.append (S.create count true) (S.create (n - count) false)

let prefix_member n p (k:nat)
  : Lemma (H.member (prefix n p) k <==> 0 < k /\ k <= n /\ k <= p) = ()

let prefix_step (n:nat) (k:nat { 0 < k /\ k <= n })
  : Lemma (H.change (prefix n (k - 1)) k true == prefix n k) =
  S.lemma_eq_intro (H.change (prefix n (k - 1)) k true) (prefix n k)

let initial n : Lemma (consistent (H.empty n) 0 (prefix n 0)) = ()

(** The next producer insertion is necessarily new and preserves every tombstone. *)
let produce s (p:nat) d
  : Lemma
      (requires consistent s p d /\ p < S.length s)
      (ensures not (H.member s (p + 1)) /\
        consistent (H.change s (p + 1) true) (p + 1) d) =
  introduce forall (k:nat).
    H.member (H.change s (p + 1) true) k ==
      (if k == p + 1 then true else H.member s k)
  with (H.change_member s (p + 1) true k)

(** Only a successful removal records a tombstone. Failed removals do not
incorrectly promise that a future producer cannot add the queried key. *)
let removed (d:S.seq bool) (k:nat { 0 < k /\ k <= S.length d }) (r:bool) =
  if r then H.change d k true else d

let consume s p d (k:nat)
  : Lemma
      (requires consistent s p d /\ 0 < k /\ k <= S.length s)
      (ensures consistent (H.change s k false) p (removed d k (H.member s k)) /\
        (H.member s k ==> H.member (removed d k (H.member s k)) k)) =
  introduce forall (j:nat).
    H.member (H.change s k false) j == (if j == k then false else H.member s j) /\
    H.member (H.change d k true) j == (if j == k then true else H.member d j)
  with (H.change_member s k false j; H.change_member d k true j)

(** A recorded removal forbids membership despite subsequent producer steps. *)
let cannot_remove_twice s p d k
  : Lemma
      (requires consistent s p d /\ H.member d k)
      (ensures not (H.member s k)) = ()

(** Once every key has a tombstone, the concrete abstract set is exactly empty. *)
let drained s p
  : Lemma
      (requires consistent s p (prefix (S.length s) (S.length s)))
      (ensures s == H.empty (S.length s)) =
  introduce forall (i:nat { i < S.length s }). S.index s i == false
  with (
    prefix_member (S.length s) (S.length s) (i + 1);
    cannot_remove_twice s p (prefix (S.length s) (S.length s)) (i + 1)
  );
  S.lemma_eq_intro s (H.empty (S.length s))
