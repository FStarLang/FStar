module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Model

(**
Pure append-only history model for the Michael--Scott FIFO example.

History contains every node ever linked, including retired dummy nodes.
Head and tail are monotone indices into that history, while the abstract
queue is the value sequence strictly AFTER head. Linking appends a value,
advancing head removes the oldest value, and advancing tail leaves the
abstract sequence unchanged. Node identities and values are generic here;
machine-word bounds and physical ownership belong to Storage and State.

This is forward, monotonic reasoning: immutable prefixes plus unique node
identities make stale observations useful without ABA or prophecy variables.
It is not a model of memory reclamation or node reuse, and it does not prove
termination. In particular, `valid` does not assume tail is at most one node
behind the final node; the safety proof only needs head <= tail < length.
*)

module S = FStar.Seq
open FStar.Preorder

(** Retained node history and current dummy/head and tail positions. Queue
values are not duplicated here: a separate map supplies immutable payloads. *)
type state (a:Type0) = {
  nodes:S.seq a;
  head:nat;
  tail:nat;
}

(** A node identity occurs at most once in the entire lifetime history.
Duplicate payload VALUES are allowed; uniqueness concerns node identities. *)
let unique (#a:Type0) (s:S.seq a) =
  forall (i j:nat). i < S.length s /\ j < S.length s /\
    S.index s i == S.index s j ==> i == j

(** Head never overtakes tail, both are in a nonempty history, and node
identities never recur. This is the invariant of all pure transitions. *)
let valid (#a:Type0) (s:state a) =
  s.head <= s.tail /\ s.tail < S.length s.nodes /\ unique s.nodes

(** Earlier history entries keep both their index and their identity. *)
let prefix (#a:Type0) (s t:S.seq a) =
  S.length s <= S.length t /\
  (forall (i:nat). i < S.length s ==> S.index s i == S.index t i)

(** Monotonic-ghost-reference relation: append-only nodes and nondecreasing
head/tail. Validity is imposed separately by the refined history type. *)
let advances (#a:Type0) : preorder (state a) =
  fun s t -> prefix s.nodes t.nodes /\ s.head <= t.head /\ s.tail <= t.tail

(** Empty queue represented by one dummy node, with head = tail = 0. *)
let singleton (#a:Type0) (x:a) : s:state a { valid s } =
  { nodes=S.create 1 x; head=0; tail=0 }

(** Live node IDs, excluding the current dummy and all retired nodes. *)
let remaining (#a:Type0) (s:state a { valid s }) =
  S.slice s.nodes (s.head + 1) (S.length s.nodes)

(** Mathematical FIFO contents used by the public operation contracts. *)
let contents (#a #b:Type0) (value:a -> b) (s:state a { valid s }) =
  S.map_seq value (remaining s)

(** Relate abstract queue size to the retained history and dummy position. *)
let contents_length (#a #b:Type0) (value:a -> b) (s:state a { valid s })
  : Lemma (S.length (contents value s) == S.length s.nodes - s.head - 1) =
  S.map_seq_len value (remaining s)

(** Translate an abstract position to its physical-history node. *)
let contents_index (#a #b:Type0) (value:a -> b) (s:state a { valid s })
  (i:nat { i + s.head + 1 < S.length s.nodes })
  : Lemma (contents_length value s;
      S.index (contents value s) i == value (S.index s.nodes (s.head + 1 + i))) =
  S.map_seq_index value (remaining s) i

(** Model successful link CAS: extend history with a fresh identity, leaving
head/tail untouched. Freshness is later obtained from exclusive node tickets. *)
let append (#a:Type0) (s:state a { valid s })
  (x:a { forall (i:nat). i < S.length s.nodes ==> not (S.index s.nodes i == x) })
  : t:state a { valid t /\ advances s t } =
  { s with nodes=S.append s.nodes (S.create 1 x) }

(** Enqueue correspondence theorem: physical-history append is FIFO append,
not merely an increase in length or preservation of well-formedness. *)
let append_contents (#a #b:Type0) (value:a -> b) (s:state a { valid s })
  (x:a { forall (i:nat). i < S.length s.nodes ==> not (S.index s.nodes i == x) })
  : Lemma (contents value (append s x) ==
      S.append (contents value s) (S.create 1 (value x))) =
  let t = append s x in
  contents_length value s;
  contents_length value t;
  let point (i:nat { i < S.length (contents value t) })
    : Lemma (S.index (contents value t) i ==
        S.index (S.append (contents value s) (S.create 1 (value x))) i) =
    contents_index value t i;
    if i < S.length (contents value s) then contents_index value s i
  in
  FStar.Classical.forall_intro point;
  assert (S.equal (contents value t)
    (S.append (contents value s) (S.create 1 (value x))))

(** Model structural helping. Tail moves to an existing successor; the
remaining sequence does not change and no client operation commits here. *)
let advance_tail (#a:Type0) (s:state a { valid s /\ s.tail + 1 < S.length s.nodes })
  : t:state a { valid t /\ advances s t /\ remaining t == remaining s } =
  { s with tail=s.tail + 1 }

(** Model successful dequeue CAS. The tail-ahead premise preserves head <=
tail after the next live node becomes the new dummy. *)
let advance_head (#a:Type0) (s:state a { valid s /\ s.head < s.tail })
  : t:state a { valid t /\ advances s t } =
  { s with head=s.head + 1 }

(** Dequeue correspondence theorem: advancing head removes exactly the
first abstract value and leaves the rest in the same order. *)
let remove_contents (#a #b:Type0) (value:a -> b)
  (s:state a { valid s /\ s.head < s.tail })
  : Lemma (contents value s ==
      S.append (S.create 1 (value (S.index s.nodes (s.head + 1))))
        (contents value (advance_head s))) =
  let t = advance_head s in
  contents_length value s;
  contents_length value t;
  let point (i:nat { i < S.length (contents value s) })
    : Lemma (S.index (contents value s) i ==
        S.index (S.append (S.create 1 (value (S.index s.nodes (s.head + 1))))
          (contents value t)) i) =
    contents_index value s i;
    if i > 0 then contents_index value t (i - 1)
  in
  FStar.Classical.forall_intro point;
  assert (S.equal (contents value s)
    (S.append (S.create 1 (value (S.index s.nodes (s.head + 1))))
      (contents value t)))

(** Prefix stability plus uniqueness turns equality of stale/current node
IDs into equality of indices, ruling out ABA in successful CAS proofs. *)
let same_node_same_index (#a:Type0) (old current:state a)
  (i j:nat)
  : Lemma
      (requires valid current /\ advances old current /\
        i < S.length old.nodes /\ j < S.length current.nodes /\
        S.index old.nodes i == S.index current.nodes j)
      (ensures i == j) =
  ()

(** If a previously observed head is still the final node at a later read,
monotonicity forces it to remain the head. This proves an empty dequeue at
the null-successor load, without a second head-validation load. *)
let empty_from_head_snapshot (#a:Type0) (old current:state a)
  : Lemma
      (requires valid old /\ valid current /\ advances old current /\
        old.head + 1 == S.length current.nodes)
      (ensures current.head == old.head /\ S.length (remaining current) == 0) =
  ()

(** List-to-sequence conversion preserves append; used to connect recursive
payload ownership to the public sequence model. *)
let rec of_list_append (#a:Type0) (xs ys:list a)
  : Lemma (ensures S.seq_of_list (FStar.List.Tot.append xs ys) ==
      S.append (S.seq_of_list xs) (S.seq_of_list ys))
      (decreases xs) =
  match xs with
  | [] ->
    S.lemma_empty (S.seq_of_list xs);
    S.append_empty_l (S.seq_of_list ys)
  | x::xs ->
    of_list_append xs ys;
    S.append_assoc (S.create 1 x) (S.seq_of_list xs) (S.seq_of_list ys)

(** Reverse conversion distributes over append for the enqueue payload proof. *)
let to_list_append (#a:Type0) (xs ys:S.seq a)
  : Lemma (S.seq_to_list (S.append xs ys) ==
      FStar.List.Tot.append (S.seq_to_list xs) (S.seq_to_list ys)) =
  of_list_append (S.seq_to_list xs) (S.seq_to_list ys);
  S.lemma_seq_to_seq_of_list (FStar.List.Tot.append (S.seq_to_list xs) (S.seq_to_list ys))

(** Identify one appended abstract value with one owned payload-list entry. *)
let to_list_singleton (#a:Type0) (x:a)
  : Lemma (S.seq_to_list (S.create 1 x) == [x]) =
  S.append_empty_r (S.create 1 x);
  S.lemma_seq_to_list_cons x S.empty
