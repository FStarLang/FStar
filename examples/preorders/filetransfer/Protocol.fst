module Protocol

open FStar.Seq

open FStar.Preorder
open FStar.Heap
open FStar.ST

(* size of each message fragment sent over the network *)
assume val fragment_size:nat

type byte

type fragment = s:seq byte{length s <= fragment_size}

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
let sender_connection_inv (c:connection) (h:heap) :GTot Type0
  = let C _ ctr msgs = c in
    sel h ctr = (length (sel h msgs))

assume val seq_map:
  #a:Type -> #b:Type -> f:(a -> b) -> s:seq a
  -> (r:seq b{length s = length r /\ (forall (i:nat). i < length s ==> index r i == f (index s i))})

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
  :ST unit (requires (fun h0 -> sender_connection_inv c h0 /\ ctr c h0 >= 1 /\
                             f == index (raw c h0) (ctr c h0 - 1)))
           (ensures  (fun h0 _ h1 -> h0 == h1))

(* type of the buffer and sender and receiver operate on *)
type iarray (n:nat) (a:Type) :Type

(* these probably need some contains precondition? *)
assume val as_seq_ghost:
  #n:nat -> #a:Type -> iarray n a -> i:nat -> j:nat{j >= i /\ j <= n} -> h:heap
  -> GTot (s:seq a{length s = j - i})
assume val as_seq:
  #n:nat -> #a:Type -> arr:iarray n a -> i:nat -> j:nat{j >= i /\ j <= n}
  -> ST (s:seq a{length s = j - i})
       (requires (fun h0 -> True))
       (ensures  (fun h0 s h1 -> h0 == h1 /\ s == as_seq_ghost arr i j h0))

assume val zeroes: n:nat -> (s:seq byte{length s = n})

let modifies (c:connection) (h0:heap) (h1:heap) :Type0
  = let C _ ctr_ref msgs_ref = c in
    modifies (Set.union (Set.singleton (addr_of ctr_ref))
                        (Set.singleton (addr_of msgs_ref))) h0 h1

assume val lemma_snoc_log
  (c:connection) (i:nat) (cipher:fragment) (msg:fragment{oplus msg ((C?.rand c) i) == cipher})
  (h0 h1:heap)
  :Lemma (requires (let C _ _ msgs_ref = c in
                    sel h1 msgs_ref == snoc (sel h0 msgs_ref) (E i cipher msg)))
	 (ensures  (log c h1 == snoc (log c h0) msg))
  
let send (#n:nat) (buf:iarray n byte) (c:connection)
  :ST nat (requires (fun h0 -> sender_connection_inv c h0))
        (ensures  (fun h0 sent h1 -> modifies c h0 h1           /\
	                          sent <= min n fragment_size /\
				  ctr c h1 = ctr c h0 + 1    /\
                                  log c h1 == snoc (log c h0)
				                   (append (as_seq_ghost buf 0 sent h0)
						           (zeroes (fragment_size - sent)))))
  = let h0 = ST.get () in
    let C rand ctr_ref msgs_ref = c in

    recall ctr_ref;
    recall msgs_ref;  //AR: these are necessary for addr_of ctr_ref <> addr_of msgs_ref
    
    let msgs0 = read msgs_ref in
    let i0 = read ctr_ref in

    let sent = min n fragment_size in
    let msg = as_seq buf 0 sent in
    let msg = append msg (zeroes (fragment_size - sent)) in
    let cipher = oplus msg (rand i0) in

    let msgs1 = snoc msgs0 (E i0 cipher msg) in
    let i1 = i0 + 1 in

    write msgs_ref msgs1;
    write ctr_ref i1;
    network_send c cipher;

    let h1 = ST.get () in
    lemma_snoc_log c i0 cipher msg h0 h1;

    sent
