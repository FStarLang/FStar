module Protocol

open FStar.Seq

open FStar.Preorder
open FStar.Heap
open FStar.ST

(* size of each message fragment sent over the network *)
assume val fragment_size:nat

type byte

type fragment = s:seq byte{length s = fragment_size}

(* random bytes for ideal cipher? *)
type randomness = nat -> fragment

assume val oplus: fragment -> fragment -> fragment

(* an entry in the message log *)
noeq type entry (rand:randomness) =
  | E: i:nat -> cipher:fragment -> msg:fragment{oplus msg (rand i) == cipher} -> entry rand

(* sequence of messages *)
type entries (rand:randomness) = s:seq (entry rand){forall (i:nat). i < length s ==> E?.i (index s i) = i}

(* counter increases monotonically *)
let counter_pre :preorder nat = fun (n1:nat) (n2:nat) -> b2t (n1 <= n2)

let is_prefix_of (#a:Type) (s1:seq a) (s2:seq a) :Type0
  = length s1 <= length s2 /\
    (forall (i:nat). i < length s1 ==> index s1 i == index s2 i)

(* entries are only appended to, typing entries_rel directly as `preorder (entries rand)` doesn't work *)
let entries_rel (rand:randomness) :relation (entries rand) =
  fun (es1:entries rand) (es2:entries rand) -> es1 `is_prefix_of` es2

let entries_pre (rand:randomness) :preorder (entries rand) = entries_rel rand

noeq type connection =
  | C: rand:randomness -> ctr:mref nat counter_pre -> msgs:mref (entries rand) (entries_pre rand) -> connection

(* for a valid connection, ctr is bounded by the length of msgs *)
let valid_connection (c:connection) (h:heap) :GTot Type0
  = let C _ ctr msgs = c in
    sel h ctr <= (length (sel h msgs))

assume val seq_map: #a:Type -> #b:Type -> (a -> b) -> seq a -> seq b

(* seq of ciphers sent so far on this connection *)
let raw (c:connection) (h:heap) :GTot (seq fragment) =
  let C _ _ msgs = c in
  seq_map (fun (E _ c _) -> c) (sel h msgs)  //writing C?.msgs doesn't work, some unification error

(* seq of plain messages sent so far on this connection *)
let log (c:connection) (h:heap) :GTot (seq fragment) =
  let C _ _ msgs = c in
  seq_map (fun (E _ _ m) -> m) (sel h msgs)

assume val lemma_prefix_entries_implies_prefix_log
  (c:connection) (h1:heap) (h2:heap)
  :Lemma (requires (let C _ _ msgs = c in
                    sel h1 msgs `is_prefix_of` sel h2 msgs))
	 (ensures  (log c h1 `is_prefix_of` log c h2))
	 [SMTPat (log c h1); SMTPat (log c h2)]

(* current counter for the connection, consider adding the valid refinement? *)
let ctr (c:connection) (h:heap) :GTot nat =
  let C _ ctr _ = c in
  sel h ctr

(* stable predicate for counter *)
let counter_pred (c:connection) (h0:heap) :(heap -> Type0) =
  let C _ cref _ = c in
  fun h -> h `contains` cref /\ ctr c h0 <= ctr c h

(* stable predicate for log *)
let log_pred (c:connection) (h0:heap) :(heap -> Type0) =
  let C _ _ msgs_ref = c in
  fun h -> h `contains` msgs_ref /\ log c h0 `is_prefix_of` log c h

let snap (c:connection) :ST unit (requires (fun _ -> True))
                                 (ensures  (fun h0 _ h1 -> witnessed (counter_pred c h0) /\
				                        witnessed (log_pred c h0)     /\
							h0 == h1))
  = let h0 = ST.get () in
    let C _ ctr_ref msgs_ref = c in
    recall ctr_ref; recall msgs_ref;
    gst_witness (counter_pred c h0); gst_witness (log_pred c h0)

(* network send is called once log had been appended to etc. *)
assume val network_send
  (c:connection) (f:fragment)
  :ST unit (requires (fun h0 -> ctr c h0 < length (raw c h0) /\ f == index (raw c h0) (ctr c h0)))
           (ensures  (fun h0 _ h1 -> h0 == h1))









