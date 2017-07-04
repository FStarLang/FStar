module Protocol

open FStar.Seq

open FStar.Preorder
open FStar.Heap
open FStar.ST

open FreezeArray

(* size of each message fragment sent over the network *)
assume val fragment_size:nat

type byte

type message  = s:seq byte{length s <= fragment_size}
type fragment = s:seq byte{length s = fragment_size}

(* random bytes for ideal cipher? *)
type randomness = nat -> fragment

assume val oplus: fragment -> fragment -> fragment

assume val lemma_oplus (a:fragment) (b:fragment)
  :Lemma (oplus (oplus a b) b == a)
   [SMTPat (oplus (oplus a b) b)]

(* a message sent on the network cannot be unsent *)
(* every fragment has a ref bool, that is initialized to false, and sending the fragment over the network sets it to true *)
let sent_pre :preorder bool = fun (b1:bool) (b2:bool) -> b1 ==> b2

assume val zeroes: n:nat -> (s:seq byte{length s = n})

let pad (m:message) :fragment = append m (zeroes (fragment_size - (length m)))

assume val unpad (s:fragment)
  :(r:(nat * message){length (snd r) = fst r /\ s == pad (snd r)})

(* an entry in the message log *)
noeq type entry (rand:randomness) =
  | E: i:nat -> msg:message -> cipher:fragment{oplus (pad msg) (rand i) == cipher} -> sent:mref bool sent_pre -> entry rand

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

(* seq of plain messages sent so far on this connection *)
let log (c:connection) (h:heap) :GTot (seq message) =
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

let sender (c:connection) :Tot bool = S? c
let receiver (c:connection) :Tot bool = R? c

let modifies_s (c:connection{sender c}) (h0:heap) (h1:heap) :Type0
  = let S _ es_ref = c in
    modifies (Set.singleton (addr_of es_ref)) h0 h1

assume val lemma_snoc_log
  (c:connection{sender c}) (i:nat) (cipher:fragment) (msg:message{oplus (pad msg) ((rand_of c) i) == cipher})
  (sent_ref:mref bool sent_pre)
  (h0 h1:heap)
  :Lemma (requires (let S _ es_ref = c in
                    sel h1 es_ref == snoc (sel h0 es_ref) (E i msg cipher sent_ref)))
	 (ensures  (log c h1 == snoc (log c h0) msg))

(* network send is called once log had been appended to etc. *)
assume val network_send
  (c:connection) (f:fragment)
  :ST unit (requires (fun h0 -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1))  //TODO: this is wrong, it modifies the sent_ref

(* TODO: we need to give some more precise type that talks about sent_refs, they are not being used currently at all *)
let send (#n:nat) (buf:iarray n byte) (c:connection{sender c})
  :ST nat (requires (fun h0 -> True))
        (ensures  (fun h0 sent h1 -> modifies_s c h0 h1            /\
	                          sent <= min n fragment_size  /\
				  ctr c h1 = ctr c h0 + 1     /\
                                  log c h1 == snoc (log c h0) (as_seq_ghost buf 0 sent h0)))
  = let h0 = ST.get () in

    recall_connection c;
    let S rand es_ref = c in

    let msgs0 = read es_ref in
    let i0 = length msgs0 in

    let sent = min n fragment_size in
    let msg = as_seq buf 0 sent in
    let frag = append msg (zeroes (fragment_size - sent)) in
    let cipher = oplus frag (rand i0) in

    let sent_ref :mref bool sent_pre = alloc false in
    let msgs1 = snoc msgs0 (E i0 msg cipher sent_ref) in

    write es_ref msgs1;    

    let h1 = ST.get () in
    lemma_snoc_log c i0 cipher msg sent_ref h0 h1;

    sent

(* seq of ciphers sent so far on this connection *)
let ciphers (c:connection) (h:heap) :GTot (seq fragment) =
  seq_map (fun (E _ _ cipher _) -> cipher) (sel h (entries_of c))

assume val network_receive
  (c:connection{receiver c})
  :ST (option fragment) (requires (fun h0          -> True))
                        (ensures  (fun h0 f_opt h1 -> h0 == h1                                       /\
						   (Some? f_opt <==> ctr c h0 < length (ciphers c h0)) /\
						   (ctr c h0 < length (ciphers c h0) ==>
						    f_opt == Some (index (ciphers c h0) (ctr c h0)))))

type array (n:nat) (a:Type) :Type

assume val arr_addr (#n:nat) (#a:Type) (arr:array n a) :GTot nat

let modifies_r (#n:nat) (#a:Type) (c:connection{receiver c}) (arr:array n a) (h0 h1:heap) :Type0
  = let R _ _ ctr_ref = c in
    modifies (Set.union (Set.singleton (addr_of ctr_ref))
                        (Set.singleton (arr_addr arr))) h0 h1

assume val all_init (#n:nat) (#a:Type) (arr:array n a) (i:nat) (j:nat{j >= i /\ j <= n}) :Type0

assume val as_seq_ghost_a:
  #n:nat -> #a:Type -> array n a -> i:nat -> j:nat{j >= i /\ j <= n} -> h:heap
  -> GTot (s:seq a{length s = j - i})

assume val fill
  (#n:nat{fragment_size <= n}) (buf:array n byte) (msg:message)
  : ST unit (requires (fun h0      -> True))
            (ensures  (fun h0 _ h1 -> modifies (Set.singleton (arr_addr buf)) h0 h1 /\ 
	                           all_init buf 0 (length msg)                    /\
	                           as_seq_ghost_a buf 0 (length msg) h1 == msg))

let receive (#n:nat{fragment_size <= n}) (buf:array n byte) (c:connection{receiver c})
  :ST (option nat) (requires (fun h0          -> True))
                 (ensures  (fun h0 r_opt h1 -> match r_opt with
					    | None   -> h0 == h1
					    | Some r ->
					      modifies_r c buf h0 h1       /\
					      r <= fragment_size            /\
					      all_init buf 0 r             /\
					      ctr c h1 = ctr c h0 + 1      /\
					      ctr c h0 < length (log c h0) /\
					      index (log c h0) (ctr c h0) == as_seq_ghost_a buf 0 r h1))
  = let h0 = ST.get () in
    let R rand es_ref ctr_ref = c in
    assume (arr_addr buf <> addr_of ctr_ref);
    assume (arr_addr buf <> addr_of es_ref);  //AR: these two should be possible to prove once we hook it up to the actual array implementation
    recall_connection c;

    match network_receive c with
    | None        -> None
    | Some cipher ->
      assert (index (ciphers c h0) (ctr c h0) == cipher);
      assume (forall (i:nat). i < (length (sel h0 (entries_of c))) ==> index (ciphers c h0) i == oplus (pad (index (log c h0) i)) (rand i));
      let i0 = read ctr_ref in
      let msg = oplus cipher (rand i0) in
      admit ();
      let len, m = unpad msg in
      assert (i0 < length (sel_tot h0 es_ref));
      gst_witness (counter_pred (i0 + 1) es_ref);
      write ctr_ref (i0 + 1);  //AR: order of this write is important ... specifically, if we write ctr_ref after arr, we need a lemma to say arr remains unchanged, once this is hooked up to actual array implementation, it shouldn't matter
      fill buf m;
      Some len

(***** sender and receiver *****)

(* assume val flatten (log:seq message) :Tot (seq byte) *)

(* assume type all_initialized:  *)

(* assume val all_init_lemma: *)
(*   (#n:nat) (file:iarray n byte) *)
(*   :Lemma (requires (all_init file)) *)
(*          (ensures  (forall (h1:heap) (h2:heap). heap_rel h1 h2 ==>  *)

(* let sent_file (#n:nat) (file:iarray n byte) (c:connection) (from:nat) (num_chunks:nat) :heap_predicate *)
(*   = fun h -> let frags, to = log c h, ctr c h in *)
(*           h `contains_connection` c /\ from + num_chunks <= length frags /\ as_seq_ghost file 0 n h == flatten (slice frags from (from + num_chunks)) *)

(* let sent_file' (#n:nat) (file:iarray n byte) (c:connection) (from:nat) (num_chunks:nat) :(p:heap_predicate{stable p}) *)
(*   = assume (forall (#a:Type) (#b:Type) (f:a -> b) (s1:seq a) (s2:seq a). s1 `is_prefix_of` s2 ==> *)
(*                                                                    seq_map f s1 `is_prefix_of` seq_map f s2); *)
(*     sent_file file c from num_chunks *)
