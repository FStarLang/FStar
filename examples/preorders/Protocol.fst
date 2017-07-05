module Protocol

open FStar.Seq

open FStar.Preorder
open FStar.Heap
open FStar.ST

open FreezingArray

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
type entries (rand:randomness) = s:seq (entry rand){forall (i:nat). i < length s ==> E?.i (Seq.index s i) = i}

let is_prefix_of (#a:Type) (s1:seq a) (s2:seq a) :Type0
  = length s1 <= length s2 /\
    (forall (i:nat). i < length s1 ==> Seq.index s1 i == Seq.index s2 i)

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
  -> (r:seq b{length s = length r /\ (forall (i:nat). i < length s ==> Seq.index r i == f (Seq.index s i))})

let rand_of (c:connection) :randomness =
  match c with
  | S r _
  | R r _ _ -> r

let entries_of (c:connection) :(mref (entries (rand_of c)) (entries_rel (rand_of c))) =
  match c with
  | S _ es   -> es
  | R _ es _ -> es

let contains_connection (h:heap) (c:connection) =
  match c with
  | S _ es_ref         -> h `contains` es_ref
  | R _ es_ref ctr_ref -> h `contains` es_ref /\ h `contains` ctr_ref

let recall_connection (c:connection) :ST unit (requires (fun h0 -> True)) (ensures (fun h0 _ h1 -> h0 == h1 /\ h0 `contains_connection` c))
  = match c with
    | S _ es_ref         -> ST.recall es_ref
    | R _ es_ref ctr_ref -> ST.recall es_ref; ST.recall ctr_ref

(* seq of plain messages sent so far on this connection *)
let log (c:connection) (h:heap{h `contains_connection` c}) :Tot (seq message) =
  seq_map (fun (E _ m _ _) -> m) (sel_tot h (entries_of c))

assume val lemma_prefix_entries_implies_prefix_log
  (c:connection) (h1:heap) (h2:heap{h1 `contains_connection` c /\ h2 `contains_connection` c})
  :Lemma (requires (sel h1 (entries_of c) `is_prefix_of` sel h2 (entries_of c)))
	 (ensures  (log c h1 `is_prefix_of` log c h2))
	 [SMTPat (log c h1); SMTPat (log c h2)]

(* current counter for the connection, consider adding the valid refinement? *)
let ctr (c:connection) (h:heap{h `contains_connection` c}) :Tot nat =
  match c with
  | S _ es_ref    -> length (sel_tot h es_ref)
  | R _ _ ctr_ref -> sel_tot h ctr_ref

(* stable predicate for counter *)
let connection_pred (c:connection) (h0:heap{h0 `contains_connection` c}) :(p:heap_predicate{stable p}) =
  fun h -> h `contains_connection` c /\
        ctr c h0 <= ctr  c h /\ ctr c h0 <= length (log c h) /\ log c h0 `is_prefix_of` log c h

let snap (c:connection) :ST unit (requires (fun _ -> True))
                                 (ensures  (fun h0 _ h1 -> h0 `contains_connection` c /\ witnessed (connection_pred c h0) /\ h0 == h1))
  = let h0 = ST.get () in
    recall_connection c;
    (match c with
     | S _ _              -> ()
     | R _ es_ref ctr_ref -> gst_recall (counter_pred (sel_tot h0 ctr_ref) es_ref));
    gst_witness (connection_pred c h0)

type array (a:Type0) (n:nat) = FreezingArray.array a n
type iarray (a:Type0) (n:nat) = FreezingArray.iarray a n

(* (\* these probably need some contains precondition? *\) *)
(* assume val as_seq_ghost: *)
(*   #n:nat -> #a:Type -> iarray n a -> i:nat -> j:nat{j >= i /\ j <= n} -> h:heap *)
(*   -> GTot (s:seq a{length s = j - i}) *)
(* assume val as_seq: *)
(*   #n:nat -> #a:Type -> arr:iarray n a -> i:nat -> j:nat{j >= i /\ j <= n} *)
(*   -> ST (s:seq a{length s = j - i}) *)
(*        (requires (fun h0 -> True)) *)
(*        (ensures  (fun h0 s h1 -> h0 == h1 /\ s == as_seq_ghost arr i j h0)) *)

let sender (c:connection) :Tot bool   = S? c
let receiver (c:connection) :Tot bool = R? c

let connection_footprint (c:connection) :GTot (Set.set nat)
  = match c with
    | S _ es_ref         -> Set.singleton (addr_of es_ref)
    | R _ es_ref ctr_ref -> Set.union (Set.singleton (addr_of es_ref)) (Set.singleton (addr_of ctr_ref))

assume val lemma_snoc_log
  (c:connection{sender c}) (i:nat) (cipher:fragment) (msg:message{oplus (pad msg) ((rand_of c) i) == cipher})
  (sent_ref:mref bool sent_pre)
  (h0:heap) (h1:heap{h0 `contains_connection` c /\ h1 `contains_connection` c})
  :Lemma (requires (let S _ es_ref = c in
                    sel h1 es_ref == snoc (sel h0 es_ref) (E i msg cipher sent_ref)))
	 (ensures  (log c h1 == snoc (log c h0) msg))

(* network send is called once log had been appended to etc. *)
assume val network_send
  (c:connection) (f:fragment)
  :ST unit (requires (fun h0 -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1))  //TODO: this is wrong, it modifies the sent_ref

(* TODO: we need to give some more precise type that talks about sent_refs, they are not being used currently at all *)
#set-options "--z3rlimit 50"
let send (#n:nat) (buf:iarray byte n) (c:connection{sender c})
  :ST nat (requires (fun h0 -> True))
        (ensures  (fun h0 sent h1 -> modifies (connection_footprint c) h0 h1         /\
	                          h0 `contains_connection` c /\
				  h1 `contains_connection` c /\
	                          sent <= min n fragment_size /\
				  ctr c h1 = ctr c h0 + 1    /\
				  (forall (i:nat). i < n ==> Some? (Seq.index (as_seq buf h0) i)) /\
                                  log c h1 == snoc (log c h0) (as_initialized_subseq buf h0 0 sent)))
  = let h0 = ST.get () in

    recall_connection c;
    recall_all_init buf;

    let S rand es_ref = c in

    let msgs0 = ST.read es_ref in
    let i0 = length msgs0 in

    let sent = min n fragment_size in
    let msg = read_subseq_i_j buf 0 sent in
    let frag = append msg (zeroes (fragment_size - sent)) in
    let cipher = oplus frag (rand i0) in

    let sent_ref :mref bool sent_pre = alloc false in
    let msgs1 = snoc msgs0 (E i0 msg cipher sent_ref) in

    ST.write es_ref msgs1;

    let h1 = ST.get () in
    lemma_snoc_log c i0 cipher msg sent_ref h0 h1;
    
    sent

(* seq of ciphers sent so far on this connection *)
let ciphers (c:connection) (h:heap) :GTot (seq fragment) =
  seq_map (fun (E _ _ cipher _) -> cipher) (sel h (entries_of c))

assume val network_receive
  (c:connection{receiver c})
  :ST (option fragment) (requires (fun h0          -> h0 `contains_connection` c))
                        (ensures  (fun h0 f_opt h1 -> h0 == h1                                           /\
			                           h0 `contains_connection` c                         /\
						   (Some? f_opt <==> ctr c h0 < length (ciphers c h0)) /\
						   (ctr c h0 < length (ciphers c h0) ==>
						    f_opt == Some (Seq.index (ciphers c h0) (ctr c h0)))))

let modifies_r (#n:nat) (c:connection{receiver c}) (arr:array byte n) (h0 h1:heap) :Type0
  = modifies (Set.union (connection_footprint c)
                        (array_footprint arr)) h0 h1

#set-options "--z3rlimit 50"
let receive (#n:nat{fragment_size <= n}) (buf:array byte n) (c:connection{receiver c})
  :ST (option nat) (requires (fun h0          -> is_mutable buf h0))
                 (ensures  (fun h0 r_opt h1 -> match r_opt with
					    | None   -> h0 == h1
					    | Some r ->
					      h0 `contains_connection` c   /\
					      h1 `contains_connection` c   /\
					      is_mutable buf h1            /\
					      modifies_r c buf h0 h1       /\
					      r <= fragment_size            /\
					      all_init_i_j buf 0 r         /\
					      ctr c h1 = ctr c h0 + 1      /\
					      ctr c h0 < length (log c h0) /\
                                              log c h0 == log c h1 /\
					      (forall (i:nat). i < r ==> Some? (Seq.index (as_seq buf h1) i)) /\
					      Seq.index (log c h0) (ctr c h0) == as_initialized_subseq buf h1 0 r))
  = let h0 = ST.get () in
    let R rand es_ref ctr_ref = c in

    assume (Set.disjoint (Set.singleton (addr_of ctr_ref)) (array_footprint buf));
    assume (Set.disjoint (Set.singleton (addr_of es_ref))  (array_footprint buf));

    recall_connection c;

    match network_receive c with
    | None        -> None
    | Some cipher ->
      let i0 = ST.read ctr_ref in
      let msg = oplus cipher (rand i0) in
      let len, m = unpad msg in

      assume (m == Seq.index (log c h0) (ctr c h0));

      gst_witness (counter_pred (i0 + 1) es_ref);
      recall_contains buf;
      ST.write ctr_ref (i0 + 1);
      fill buf m;
      Some len
#reset-options

(***** sender and receiver *****)

let lemma_is_prefix_of_slice
  (#a:Type0) (s1:seq a) (s2:seq a{s1 `is_prefix_of` s2}) (i:nat) (j:nat{j >= i /\ j <= Seq.length s1})
  :Lemma (requires True)
         (ensures  (Seq.slice s1 i j == Seq.slice s2 i j))
	 [SMTPat (s1 `is_prefix_of` s2); SMTPat (Seq.slice s1 i j); SMTPat (Seq.slice s2 i j)]
  = admit ()

assume val flatten (s:seq message) :Tot (seq byte)

assume val lemma_flatten_snoc (s:seq message) (m:message)
  :Lemma (requires True)
         (ensures  (flatten (snoc s m) == append (flatten s) m))

assume val flatten_empty (u:unit) : Lemma 
  (flatten Seq.createEmpty == Seq.createEmpty)
  
let sent_file_pred' (file:seq byte) (c:connection) (from:nat) (to:nat{from <= to}) :heap_predicate
  = fun h -> h `contains_connection` c /\ 
          (let log   = log c h in
           to <= Seq.length log /\ 
	   file == flatten (Seq.slice log from to))

let sent_file_pred (file:seq byte) (c:connection) (from:nat) (to:nat{from <= to}) :(p:heap_predicate{stable p})
  = sent_file_pred' file c from to

(* let sent_file_pred_init (file:seq byte) (c:connnection) (from:nat) (h:heap{h `contains_connection` c)} *)
(*   : Lemma (send_file_pred file c from from h) *)
(*   = assert  *)
let sent_file (file:seq byte) (c:connection) =
  exists (from:nat) (to:nat{from <= to}). witnessed (sent_file_pred file c from to)

let lemma_get_equivalent_append
  (#a:Type0) (s1:seq (option a){forall (i:nat). i < Seq.length s1 ==> Some? (Seq.index s1 i)})
  (s2:seq (option a)) (s3:seq (option a))
  :Lemma (requires (s1 == Seq.append s2 s3))
         (ensures  ((forall (i:nat). i < Seq.length s2 ==> Some? (Seq.index s2 i)) /\
	            (forall (i:nat). i < Seq.length s3 ==> Some? (Seq.index s3 i)) /\
	            get_equivalent_seq s1 == Seq.append (get_equivalent_seq s2) (get_equivalent_seq s3)))
  = admit ()

#set-options "--z3rlimit 20"
let iarray_as_seq (#a:Type) (#n:nat) (x:iarray a n) : ST (seq a) 
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->  
              h0==h1 /\
              (forall (k:nat). k < n ==> Some? (Seq.index (as_seq x h0) k)) /\
              s == as_initialized_subseq x h0 0 n))
  = admit()              
  
let send (#n:nat) (file:iarray byte n) (c:connection{sender c /\ Set.disjoint (connection_footprint c) (array_footprint file)})
  : ST unit 
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 ->
                      modifies (connection_footprint c) h0 h1 /\
                      h1 `contains_connection` c /\
                      (forall (k:nat). k < n ==> Some? (Seq.index (as_seq file h0) k)) /\
                      sent_file (as_initialized_seq file h0) c))
  = let h0 = ST.get () in
    recall_all_init file;
    recall_contains file;
    recall_connection c;
    let file_bytes0 = iarray_as_seq file in
    let from = ctr c h0 in
    let rec aux (pos:nat{pos <= n}) // (num_chunks:nat)
      :ST unit 
            (requires (fun h0 -> 
                      (forall (k:nat). k < n ==> Some? (Seq.index (as_seq file h0) k)) /\
                      h0 `contains_connection` c /\
                      from <= ctr c h0 /\
                      sent_file_pred (as_initialized_subseq file h0 0 pos) c from (ctr c h0) h0))
             (ensures  (fun h0 _ h1 -> 
                      modifies (connection_footprint c) h0 h1 /\
                      h1 `contains_connection` c /\
                      from <= ctr c h1 /\
                      (forall (k:nat). k < n ==> Some? (Seq.index (as_seq file h0) k)) /\
                      sent_file_pred (as_initialized_seq file h0) c from (ctr c h1) h1))
      = admit()
    in
    assert (Seq.equal (as_initialized_subseq file h0 0 0) Seq.createEmpty);
    flatten_empty();
    assert (Seq.equal (flatten (Seq.slice (log c h0) from from)) Seq.createEmpty);
    aux 0;
    let h1 = ST.get () in
    let file_bytes1 = iarray_as_seq file in
    assert (file_bytes0 == file_bytes1);
    gst_witness (sent_file_pred file_bytes0 c from (ctr c h1));
    assert (sent_file file_bytes0 c)



    (*   recall_all_init file; *)
    (*     recall_contains file; *)
    (*     recall_connection c; *)

    (*     assume (Set.disjoint (connection_footprint c) (array_footprint file)); *)

    (*     if pos = n then num_chunks *)
    (*     else begin *)
    (*       let sub_file = suffix file pos in *)
    (*       lemma_all_init_i_j_sub file pos (n - pos); *)
       
    (*       let h0 = ST.get () in *)
    (*       let log0 = log c h0 in *)
    (*       let sent = send sub_file c in *)
    (*       let h1 = ST.get () in *)
    (*       let log1 = log c h1 in *)

    (*       assume (log1 == snoc log0 (as_initialized_subseq file h0 pos (pos + sent))); *)

    (*       admit (); *)
    (*       aux (pos + sent) (num_chunks + 1) *)
    (*     end *)
    (* in *)



          (* assert (pos + num_sent <= n); *)
          (* let num_chunks = num_chunks + 1 in *)

          (* assert (from + num_chunks <= Seq.length log1); *)

	  (* assume (Seq.slice (as_seq file h0) 0 (pos + num_sent) == *)
	  (*         Seq.append (Seq.slice (as_seq file h0) 0 pos) (Seq.slice (as_seq file h0) pos (pos + num_sent))); *)
	  (* lemma_get_equivalent_append (Seq.slice (as_seq file h0) 0 (pos + num_sent)) *)
	  (*                             (Seq.slice (as_seq file h0) 0 pos) (Seq.slice (as_seq file h0) pos (pos + num_sent)); *)

          (* assert (as_initialized_subseq file h0 0 (pos + num_sent) == *)
	  (*         Seq.append (as_initialized_subseq file h0 0 pos) (as_initialized_subseq file h0 pos (pos + num_sent))); *)
          

          (* assert (log1 ==  *)


