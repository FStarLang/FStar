module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage
#lang-pulse

(**
Intrusive arena storage and ownership accounting for the FIFO proof.

Existing Pulse CAS primitives operate on UInt32, so nodes are indexed by
UInt32 IDs in an immutable list of cells rather than by a new pointer-CAS
axiom. Each cell has an immutable value and an atomic next field. A ticket
owns that next field exclusively at null and is consumed on first linking.

`links` retains ownership of EVERY history node, including retired dummies;
`payloads` owns resources only for values still queued. Separating these is
essential: dequeue returns the payload but never returns a node ticket.
Freshness follows from permission inconsistency, not an assumed allocator.

This is a finite lifetime allocation budget, not a recycling bounded queue.
There is no reclamation, address reuse, hazard-pointer/epoch proof, or
allocation-performance claim (arena lookup is list indexing). These limits
enable persistent history observations without prophecies or ABA handling.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.ForEvery
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module U32 = FStar.UInt32
module L = FStar.List.Tot
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Model

(** Immutable cell metadata; only the boxed next field is mutated. *)
noeq type cell = { next:B.box U32.t; value:U32.t }
(** Nonempty arena with enough UInt32 space to keep null outside valid IDs.
The type alone does not grant ownership of any contained next field. *)
type arena = cells:list cell { 0 < L.length cells /\ L.length cells < 4294967295 }
(** In-bounds machine-word node identifier for this particular arena. *)
type id (cells:arena) = n:U32.t { U32.v n < L.length cells }
(** Sentinel excluded by the arena bound; never an allocated node ID. *)
let null = 0xfffffffful
(** Pure lookup of metadata. Dereferencing next still requires ownership. *)
let at (cells:arena) (n:id cells) = L.index cells (U32.v n)
(** Immutable value associated with an ID, used by the abstract sequence map. *)
let value (cells:arena) (n:id cells) = (at cells n).value

(** Required next value at a history position: the following ID or null. *)
let successor (cells:arena) (ns:S.seq (id cells)) (k:nat { k < S.length ns }) =
  if k + 1 < S.length ns then S.index ns (k + 1) else null

(** Exclusive next-field ownership for one position; emp outside the domain
supports the finite multiplicative-quantifier combinators below. *)
let link (cells:arena) (ns:S.seq (id cells)) (k:nat) =
  if k < S.length ns
  then B.pts_to (at cells (S.index ns k)).next (successor cells ns k)
  else emp

(** Separating ownership of every physical link in the retained history.
`forall+` is multiplicative, unlike the AU closing choice's additive forall*. *)
let links (cells:arena) (ns:S.seq (id cells)) =
  forall+ (k:nat { k < S.length ns }). link cells ns k

(** All links except k, used while one read/CAS focuses the k-th next field. *)
let rest (cells:arena) (ns:S.seq (id cells)) (k:nat) =
  forall+ (j:nat { j < S.length ns /\ j =!= k }). link cells ns j

(** One-use enqueue permission. A linked node's next field stays in links
forever, even if it is null or its payload has already been dequeued. *)
let ticket (cells:arena) (n:id cells) = B.pts_to (at cells n).next null

(** Physical box ownership is transferable across worker localities. *)
instance send_link cells ns k : is_send (link cells ns k) =
  if k < S.length ns
  then B.is_send_pts_to (at cells (S.index ns k)).next #1.0R (successor cells ns k)
  else is_send_placeless emp

(** Transferability of the entire finite separating collection of links. *)
instance send_links cells ns : is_send (links cells ns) =
  is_send_forevery (fun (k:nat { k < S.length ns }) -> link cells ns k)
    #(fun k -> send_link cells ns k)

(** Extract one next field, retaining all other links as a separating frame. *)
ghost fn focus (cells:arena) (ns:S.seq (id cells)) (k:nat { k < S.length ns })
  requires links cells ns
  ensures rest cells ns k **
    B.pts_to (at cells (S.index ns k)).next (successor cells ns k)
{
  unfold links;
  forevery_remove' #nat (fun j -> j < S.length ns) (link cells ns) k;
  fold rest cells ns k;
  rewrite link cells ns k as
    B.pts_to (at cells (S.index ns k)).next (successor cells ns k);
}

(** Reinsert a focused field whose value still agrees with the same history.
Successful linking instead uses append_link for the extended history. *)
ghost fn restore (cells:arena) (ns:S.seq (id cells)) (k:nat { k < S.length ns })
  requires rest cells ns k **
    B.pts_to (at cells (S.index ns k)).next (successor cells ns k)
  ensures links cells ns
{
  unfold rest;
  rewrite B.pts_to (at cells (S.index ns k)).next (successor cells ns k)
    as link cells ns k;
  forevery_insert #(nat) #(fun j -> j < S.length ns /\ j =!= k) (link cells ns) k;
  forevery_refine_ext #nat (fun j -> j < S.length ns) (link cells ns);
  fold links cells ns;
}

(** Consume the dummy's ticket to create the initial one-node link collection. *)
ghost fn singleton (cells:arena) (n:id cells)
  requires ticket cells n
  ensures links cells (S.create 1 n)
{
  unfold ticket;
  forevery_intro_false #nat (link cells (S.create 1 n));
  rewrite B.pts_to (at cells n).next null as link cells (S.create 1 n) 0;
  forevery_insert #nat #(fun _ -> False) (link cells (S.create 1 n)) 0;
  forevery_refine_ext #nat (fun j -> j < S.length (S.create 1 n))
    (link cells (S.create 1 n));
  fold links cells (S.create 1 n);
}

(** Derive freshness from ownership: if n occurred in ns, its link and ticket
would own two full permissions to the same next field. This contradiction
also rules out re-enqueueing retired nodes without a separate no-reuse axiom. *)
ghost fn ticket_is_fresh (cells:arena) (ns:S.seq (id cells)) (n:id cells)
  preserves links cells ns ** ticket cells n
  ensures pure (forall (k:nat). k < S.length ns ==> not (S.index ns k == n))
{
  let present = FStar.IndefiniteDescription.strong_excluded_middle
    (exists (k:nat). k < S.length ns /\ S.index ns k == n);
  if present {
    let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun (k:nat) -> k < S.length ns /\ S.index ns k == n);
    focus cells ns k;
    unfold ticket;
    rewrite each (S.index ns k) as n;
    B.gather (at cells n).next;
    B.to_ref_pts_to (at cells n).next;
    R.pts_to_perm_bound (B.box_to_ref (at cells n).next);
    assert pure False;
    unreachable ();
  }
}

(** After successful null-to-n CAS at the old last node, consume n's ticket
and extend the link collection. This is spatial bookkeeping; the caller
separately proves pure history validity and updates payload/model ownership. *)
ghost fn append_link (cells:arena) (ns:S.seq (id cells) { 0 < S.length ns })
  (n:id cells)
  requires rest cells ns (S.length ns - 1) **
    B.pts_to (at cells (S.index ns (S.length ns - 1))).next n **
    ticket cells n
  ensures links cells (S.append ns (S.create 1 n))
{
  unfold rest;
  let ns' = S.append ns (S.create 1 n);
  forevery_ext
    (fun (j:nat { j < S.length ns /\ j =!= (S.length ns - 1 <: nat) }) -> link cells ns j)
    (fun j -> link cells ns' j);
  rewrite B.pts_to (at cells (S.index ns (S.length ns - 1))).next n
    as link cells ns' (S.length ns - 1);
  forevery_insert #nat #(fun j -> j < S.length ns /\ j =!= (S.length ns - 1 <: nat))
    (link cells ns') (S.length ns - 1);
  forevery_refine_ext #nat (fun j -> j < S.length ns) (link cells ns');
  unfold ticket;
  rewrite B.pts_to (at cells n).next null as link cells ns' (S.length ns);
  forevery_insert #nat #(fun j -> j < S.length ns) (link cells ns') (S.length ns);
  forevery_refine_ext #nat (fun j -> j < S.length ns') (link cells ns');
  fold links cells ns';
  rewrite each ns' as (S.append ns (S.create 1 n));
}

(** One separating payload resource per live value, in FIFO order. P may
express exclusive external ownership, not just a pure assertion on values. *)
let rec payloads (p:U32.t -> slprop) (xs:list U32.t) : slprop =
  match xs with
  | [] -> emp
  | x::xs -> p x ** payloads p xs

(** Structural proof of sendability, requiring it for each payload P x. *)
let rec send_payloads_aux (p:U32.t -> slprop) (xs:list U32.t)
  (send_p:(x:U32.t -> is_send (p x))) : Tot (is_send (payloads p xs)) (decreases xs) =
  match xs with
  | [] -> is_send_placeless emp
  | x::xs -> is_send_star (p x) (payloads p xs) #(send_p x) #(send_payloads_aux p xs send_p)

(** Typeclass wrapper used when sending the queue invariant to workers. *)
instance send_payloads p xs {| send_p:(x:U32.t -> is_send (p x)) |}
  : is_send (payloads p xs) = send_payloads_aux p xs send_p

(** Transfer a new payload into the end of the owned FIFO, framing all
existing payloads. Dequeue later unfolds the front to return exactly P x. *)
ghost fn rec append_payload (p:U32.t -> slprop) (xs:list U32.t) (x:U32.t)
  requires payloads p xs ** p x
  ensures payloads p (L.append xs [x])
  decreases xs
{
  unfold payloads p xs;
  match xs {
    [] -> {
      fold payloads p [];
      fold payloads p [x];
    }
    y::ys -> {
      append_payload p ys x;
      fold payloads p (y::L.append ys [x]);
    }
  }
}
