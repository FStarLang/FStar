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

assume val lemma_oplus (a:fragment) (b:fragment)
  :Lemma (oplus (oplus a b) b == a)
   [SMTPat (oplus (oplus a b) b)]

(* a message sent on the network cannot be unsent *)
let sent_pre :preorder bool = fun (b1:bool) (b2:bool) -> b1 ==> b2

(* an entry in the message log *)
noeq type entry (rand:randomness) =
  | E: i:nat -> msg:fragment -> cipher:fragment{oplus msg (rand i) == cipher} -> sent:mref bool sent_pre -> entry rand

(* sequence of messages *)
type entries (rand:randomness) = s:seq (entry rand){forall (i:nat). i < length s ==> E?.i (index s i) = i}

let is_prefix_of (#a:Type) (s1:seq a) (s2:seq a) :Type0
  = length s1 <= length s2 /\
    (forall (i:nat). i < length s1 ==> index s1 i == index s2 i)

(* entries are only appended to, typing entries_rel directly as `preorder (entries rand)` doesn't work *)
let entries_rel (rand:randomness) :relation (entries rand) =
  fun (es1:entries rand) (es2:entries rand) -> es1 `is_prefix_of` es2

let entries_pre (rand:randomness) :preorder (entries rand) = entries_rel rand

(* a single state stable predicate on the counter, saying that it is less than the length of the log *)
let counter_pred (#rand:randomness) (n:nat) (es_ref:mref (entries rand) (entries_rel rand)) :(p:heap_predicate{stable p})
  = fun h -> h `contains` es_ref /\ n <= length (sel h es_ref)

(* counter type is a nat, witnessed with counter_pred *)
type counter_t (#rand:randomness) (es_ref:mref (entries rand) (entries_rel rand))
  = n:nat{witnessed (counter_pred n es_ref)}

(* counter increases monotonically *)
let counter_rel (#rand:randomness) (es_ref:mref (entries rand) (entries_rel rand)) :relation (counter_t es_ref)
  = fun n1 n2 -> b2t (n1 <= n2)

let counter_pre (#rand:randomness) (es_ref:mref (entries rand) (entries_rel rand)) :preorder (counter_t es_ref)
  = counter_rel es_ref

noeq type connection =
  | S: rand:randomness -> entries:mref (entries rand) (entries_rel rand) -> connection
  | R: rand:randomness -> entries:mref (entries rand) (entries_rel rand)
       -> ctr:mref (counter_t entries) (counter_pre entries) -> connection

assume val seq_map:
  #a:Type -> #b:Type -> f:(a -> b) -> s:seq a
  -> (r:seq b{length s = length r /\ (forall (i:nat). i < length s ==> index r i == f (index s i))})

let rand_of (c:connection) :randomness =
  match c with
  | S r _
  | R r _ _ -> r

let entries_of (c:connection) :(mref (entries (rand_of c)) (entries_rel (rand_of c))) =
  match c with
  | S _ es   -> es
  | R _ es _ -> es

(* seq of ciphers sent so far on this connection *)
(* let raw (c:connection) (h:heap) :GTot (seq fragment) = *)
(*   let C _ _ msgs = c in *)
(*   seq_map (fun (E _ c _) -> c) (sel h msgs)  //writing C?.msgs doesn't work, some unification error *)

(* seq of plain messages sent so far on this connection *)
let log (c:connection) (h:heap) :GTot (seq fragment) =
  seq_map (fun (E _ m _ _) -> m) (sel h (entries_of c))

assume val lemma_prefix_entries_implies_prefix_log
  (c:connection) (h1:heap) (h2:heap)
  :Lemma (requires (sel h1 (entries_of c) `is_prefix_of` sel h2 (entries_of c)))
	 (ensures  (log c h1 `is_prefix_of` log c h2))
	 [SMTPat (log c h1); SMTPat (log c h2)]

(* current counter for the connection, consider adding the valid refinement? *)
let ctr (c:connection) (h:heap) :GTot nat =
  match c with
  | S _ es_ref    -> length (sel h es_ref)
  | R _ _ ctr_ref -> sel h ctr_ref

let contains_connection (h:heap) (c:connection) =
  match c with
  | S _ es_ref         -> h `contains` es_ref
  | R _ es_ref ctr_ref -> h `contains` es_ref /\ h `contains` ctr_ref

let recall_connection (c:connection) :ST unit (requires (fun h0 -> True)) (ensures (fun h0 _ h1 -> h0 == h1 /\ h0 `contains_connection` c))
  = match c with
    | S _ es_ref         -> recall es_ref
    | R _ es_ref ctr_ref -> recall es_ref; recall ctr_ref

(* stable predicate for counter *)
let connection_pred (c:connection) (h0:heap) :(p:heap_predicate{stable p}) =
  fun h -> h `contains_connection` c /\
        ctr c h0 <= ctr  c h /\ ctr c h0 <= length (log c h) /\ log c h0 `is_prefix_of` log c h

let snap (c:connection) :ST unit (requires (fun _ -> True))
                                 (ensures  (fun h0 _ h1 -> witnessed (connection_pred c h0) /\ h0 == h1))
  = let h0 = ST.get () in
    recall_connection c;
    (match c with
     | S _ _              -> ()
     | R _ es_ref ctr_ref -> gst_recall (counter_pred (sel_tot h0 ctr_ref) es_ref));
    gst_witness (connection_pred c h0)

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

let modifies_s (c:connection) (h0:heap) (h1:heap) :Type0
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
        (ensures  (fun h0 sent h1 -> sender_connection_inv c h1 /\ 
	                          modifies_s c h0 h1            /\
	                          sent <= min n fragment_size  /\
				  ctr c h1 = ctr c h0 + 1     /\
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

let receiver_connection_inv (c:connection) (h:heap) :GTot Type0
  = let C _ ctr_ref msgs_ref = c in
    sel h ctr_ref <= length (sel h msgs_ref)

assume val network_receive
  (c:connection)
  :ST (option fragment) (requires (fun h0          -> receiver_connection_inv c h0))
                        (ensures  (fun h0 f_opt h1 -> receiver_connection_inv c h0                   /\
			                           h0 == h1                                       /\
						   (Some? f_opt <==> ctr c h0 < length (raw c h0)) /\
						   (ctr c h0 < length (raw c h0) ==>
						    f_opt == Some (index (raw c h0) (ctr c h0)))))

type array (n:nat) (a:Type) :Type

assume val arr_addr (#n:nat) (#a:Type) (arr:array n a) :GTot nat

let modifies_r (#n:nat) (#a:Type) (c:connection) (arr:array n a) (h0 h1:heap) :Type0
  = let C _ ctr_ref _ = c in
    modifies (Set.union (Set.singleton (addr_of ctr_ref))
                        (Set.singleton (arr_addr arr))) h0 h1

assume val all_init (#n:nat) (#a:Type) (arr:array n a) (i:nat) (j:nat{j >= i /\ j <= n}) :Type0

assume val as_seq_ghost_a:
  #n:nat -> #a:Type -> array n a -> i:nat -> j:nat{j >= i /\ j <= n} -> h:heap
  -> GTot (s:seq a{length s = j - i})

assume val unpad (s:fragment)
  :(r:(nat * seq byte){fst r <= fragment_size /\ length (snd r) = fst r /\
                     s == append (snd r) (zeroes (fragment_size - fst r))})

assume val fill
  (#n:nat{fragment_size <= n}) (m_len:nat{m_len <= fragment_size})
  (buf:array n byte) (msg:seq byte{length msg = m_len})
  : ST unit (requires (fun h0      -> True))
            (ensures  (fun h0 _ h1 -> modifies (Set.singleton (arr_addr buf)) h0 h1 /\ 
	                           all_init buf 0 m_len                           /\
	                           as_seq_ghost_a buf 0 m_len h1 == msg))

let receive (#n:nat{fragment_size <= n}) (buf:array n byte) (c:connection)
  :ST (option nat) (requires (fun h0          -> receiver_connection_inv c h0))
                 (ensures  (fun h0 r_opt h1 -> match r_opt with
					    | None   -> h0 == h1
					    | Some r ->
					      receiver_connection_inv c h1 /\
					      modifies_r c buf h0 h1       /\
					      r <= fragment_size            /\
					      all_init buf 0 r             /\
					      ctr c h1 = ctr c h0 + 1      /\
					      ctr c h0 < length (log c h0) /\
					      index (log c h0) (ctr c h0) ==
					      append (as_seq_ghost_a buf 0 r h1) (zeroes (fragment_size - r))))
  = let h0 = ST.get () in
    let C rand ctr_ref msgs_ref = c in
    assume (arr_addr buf <> addr_of ctr_ref);
    assume (arr_addr buf <> addr_of msgs_ref);  //AR: these two should be possible to prove once we hook it up to the actual array implementation
    recall ctr_ref;
    recall msgs_ref;

    match network_receive c with
    | None        -> None
    | Some cipher ->
      let i0 = read ctr_ref in
      let msg = oplus cipher (rand i0) in
      let len, m = unpad msg in
      write ctr_ref (i0 + 1);  //AR: order of this write is important ... specifically, if we write ctr_ref after arr, we need a lemma to say arr remains unchanged, once this is hooked up to actual array implementation, it shouldn't matter
      fill len buf m;
      Some len

