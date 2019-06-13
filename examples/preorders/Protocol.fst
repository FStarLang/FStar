(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Protocol

open FStar.Seq

open FStar.Preorder
open FStar.Heap
open FStar.ST

open MonotonicArray

(***** an unstable sequence proof *****)

let lemma_seq_append_unstable (#a:Type0) (s:seq a) (s1:seq a) (s2:seq a) (s3:seq a) (pos:nat) (sent:nat{pos + sent <= length s})
  :Lemma (requires (s1 == slice s 0 pos /\ s2 == slice s pos (pos + sent) /\ s3 == slice s 0 (pos + sent)))
         (ensures  (s3 == append s1 s2))
  = assert (Seq.equal s3 (append s1 s2))

(***** basic messages interface *****)

(* size of each message fragment sent over the network *)
assume val fragment_size:nat

type byte
assume val zero_b:byte

type message = s:seq byte{length s <= fragment_size}
type network_message = s:seq byte{length s = fragment_size}

(* random bytes for ideal cipher *)
type randomness = nat -> network_message

(* the xor operation on fragments *)
assume val xor: network_message -> network_message -> network_message

(* basic lemma about xor *)
assume val lemma_xor (a:network_message) (b:network_message)
  :Lemma (xor (xor a b) b == a)
   [SMTPat (xor (xor a b) b)]

val zeroes: n:nat -> (s:seq byte{length s = n})
let zeroes n = Seq.create n (zero_b)

let pad (m:message) :network_message = append m (zeroes (fragment_size - (length m)))

(* an unpad function that strips off the trailing pad *)
assume val unpad (s:network_message)
  :(r:(nat * message){length (snd r) = fst r /\ s == pad (snd r)})

assume val lemma_pad_unpad (x:unit) :Lemma (ensures (forall (m:message). snd (unpad (pad m)) == m))

(* a MAC function, returning a tag *)
assume val mac: cipher:network_message -> i:nat -> seq byte

(* an entry in the message log *)
noeq type entry (rand:randomness) =
  | E: i:nat -> msg:message -> cipher:network_message{xor (pad msg) (rand i) == cipher} -> tag:seq byte{tag == mac cipher i}
       -> entry rand

(* sequence of messages *)
type entries (rand:randomness) = s:seq (entry rand){forall (i:nat). i < length s ==> E?.i (Seq.index s i) = i}

let is_prefix_of (#a:Type) (s1:seq a) (s2:seq a) :Type0
  = length s1 <= length s2 /\
    (forall (i:nat). i < length s1 ==> Seq.index s1 i == Seq.index s2 i)

(* entries are only appended to *)
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

let rand_of (c:connection) :randomness =
  match c with
  | S r _
  | R r _ _ -> r

let entries_of (c:connection) :(mref (entries (rand_of c)) (entries_rel (rand_of c))) =
  match c with
  | S _ es   -> es
  | R _ es _ -> es

let live_connection (h:heap) (c:connection) =
  match c with
  | S _ es_ref         -> h `contains` es_ref
  | R _ es_ref ctr_ref -> h `contains` es_ref /\ h `contains` ctr_ref

let recall_connection_liveness (c:connection)
  :ST unit (requires (fun h0 -> True)) (ensures (fun h0 _ h1 -> h0 == h1 /\ h0 `live_connection` c))
  = match c with
    | S _ es_ref         -> ST.recall es_ref
    | R _ es_ref ctr_ref -> ST.recall es_ref; ST.recall ctr_ref

let lemma_sel_entries_equals_sel_tot_entries (c:connection) (h:heap)
  :Lemma (requires (h `live_connection` c))
         (ensures  (sel_tot h (entries_of c) == sel h (entries_of c)))
	 [SMTPat (sel_tot h (entries_of c))]
  = Heap.lemma_sel_equals_sel_tot_for_contained_refs h (entries_of c)

let lemma_sel_ctr_ref_equals_sel_tot_ctr_ref (c:connection{R? c}) (h:heap)
  :Lemma (requires (h `live_connection` c))
         (ensures  (let R _ _ ctr_ref = c in sel_tot h ctr_ref == sel h ctr_ref))
	 [SMTPat (sel_tot h (R?.ctr c))]
  = Heap.lemma_sel_equals_sel_tot_for_contained_refs h (R?.ctr c)

(* seq of plain messages sent so far on this connection *)
let log (c:connection) (h:heap{h `live_connection` c}) :Tot (seq message) =
  ArrayUtils.seq_map (fun (E _ m _ _) -> m) (sel_tot h (entries_of c))

let lemma_prefix_entries_implies_prefix_log
  (c:connection) (h1:heap) (h2:heap{h1 `live_connection` c /\ h2 `live_connection` c})
  :Lemma (requires (sel h1 (entries_of c) `is_prefix_of` sel h2 (entries_of c)))
	 (ensures  (log c h1 `is_prefix_of` log c h2))
	 [SMTPat (log c h1); SMTPat (log c h2)]
  = ArrayUtils.lemma_map_commutes_with_prefix (fun (E _ m _ _) -> m) (sel h1 (entries_of c)) (sel h2 (entries_of c))

(* current counter for the connection *)
let ctr (c:connection) (h:heap{h `live_connection` c}) :Tot nat =
  if S? c then length (sel_tot h (entries_of c))
  else sel_tot h (R?.ctr c)

(* recall_counter, as mentioned in the paper *)
let recall_counter (c:connection)
  :ST unit (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1 /\ h0 `live_connection` c /\ ctr c h0 <= Seq.length (log c h0)))
  = recall_connection_liveness c;
    match c with
    | S _ _              -> ()
    | R _ es_ref ctr_ref -> let n = !ctr_ref in gst_recall (counter_pred n es_ref)

(* stable predicate for counter *)
let snapshot (c:connection) (h0:heap{h0 `live_connection` c}) :(p:heap_predicate{stable p}) =
  fun h -> h `live_connection` c /\
        ctr c h0 <= ctr  c h /\ ctr c h0 <= Seq.length (log c h) /\ log c h0 `is_prefix_of` log c h

let snap (c:connection) :ST unit (requires (fun _ -> True))
                                 (ensures  (fun h0 _ h1 -> h0 `live_connection` c /\ witnessed (snapshot c h0) /\ h0 == h1))
  = let h0 = ST.get () in
    recall_connection_liveness c;
    recall_counter c;
    gst_witness (snapshot c h0)

type iarray (a:Type0) (n:nat) = x:array a n{all_init x}

let sender (c:connection)   :Tot bool = S? c //in the POPL'18 paper we present these definitions using auxiliary function
let receiver (c:connection) :Tot bool = R? c //`is_receiver` that is essentially defined as `is_receiver c = R? c`

let connection_footprint (c:connection) :GTot (Set.set nat)
  = match c with
    | S _ es_ref         -> Set.singleton (addr_of es_ref)
    | R _ es_ref ctr_ref -> Set.union (Set.singleton (addr_of es_ref)) (Set.singleton (addr_of ctr_ref))

let lemma_snoc_log
  (c:connection{sender c}) (i:nat) (cipher:network_message) (msg:message{xor (pad msg) ((rand_of c) i) == cipher})
  (tag:seq byte{tag == mac cipher i})
  (h0:heap) (h1:heap{h0 `live_connection` c /\ h1 `live_connection` c})
  :Lemma (requires (sel h1 (entries_of c) == snoc (sel h0 (entries_of c)) (E i msg cipher tag)))
	 (ensures  (log c h1 == snoc (log c h0) msg))
  = ArrayUtils.lemma_map_commutes_with_snoc (fun (E _ m _ _) -> m) (sel h0 (entries_of c)) (E i msg cipher tag)

(* network send, actually sends bytes on the network, once the log has been prepared *)
assume val network_send
  (c:connection{sender c}) (f:network_message) (tag:seq byte)
  :ST unit (requires (fun h0 -> h0 `live_connection` c /\ 
                             (let S _ es_ref = c in
                              let es = sel h0 es_ref in
			      Seq.length es > 0 /\
                              (let E _ _ c t = Seq.index es (Seq.length es - 1) in
			       c == f /\ t == tag))))
           (ensures  (fun h0 _ h1 -> h0 == h1))

(* protocol send operation *)
#set-options "--z3rlimit 50"
let send (#n:nat) (buf:iarray byte n) (c:connection{sender c})
  :ST nat (requires (fun h0 -> True))
        (ensures  (fun h0 sent h1 -> modifies (connection_footprint c) h0 h1         /\
	                          h0 `live_connection` c /\
				  h1 `live_connection` c /\
	                          sent <= min n fragment_size /\
				  ctr c h1 = ctr c h0 + 1    /\
				  (forall (i:nat). i < n ==> Some? (Seq.index (as_seq buf h0) i)) /\
                                  log c h1 == snoc (log c h0) (as_initialized_subseq buf h0 0 sent)))
  = let h0 = ST.get () in

    recall_connection_liveness c;
    recall_all_init buf;

    let S rand es_ref = c in

    let msgs0 = ST.read es_ref in
    let i0 = length msgs0 in

    let sent = min n fragment_size in
    let msg = read_subseq_i_j buf 0 sent in
    let frag = append msg (zeroes (fragment_size - sent)) in
    let cipher = xor frag (rand i0) in

    let msgs1 = snoc msgs0 (E i0 msg cipher (mac cipher i0)) in

    ST.write es_ref msgs1;

    network_send c cipher (mac cipher i0);
    let h1 = ST.get () in
    lemma_snoc_log c i0 cipher msg (mac cipher i0) h0 h1;
    
    sent

(* seq of ciphers sent so far on this connection *)
let ciphers (c:connection) (h:heap) :GTot (seq network_message) =
  ArrayUtils.seq_map E?.cipher (sel h (entries_of c))

assume val network_receive (c:connection)
  :ST (option (network_message * seq byte)) (requires (fun h0 -> h0 `live_connection` c))
                                     (ensures  (fun h0 _ h1 -> h0 == h1))

let modifies_r (#n:nat) (c:connection{receiver c}) (arr:array byte n) (h0 h1:heap) :Type0
  = modifies (Set.union (connection_footprint c)
                        (array_footprint arr)) h0 h1

assume val verify (c:connection{receiver c}) (cipher:network_message) (tag:seq byte) (i:nat)
  :ST bool (requires (fun h0 -> h0 `live_connection` c))
           (ensures  (fun h0 r h1 -> h0 == h1 /\
	              (r ==>
	               (let R _ es_ref _ = c in
		        let es = sel h0 es_ref in
			i < Seq.length es /\
			(let E _ _ c t = Seq.index es i in
			 c == cipher /\ t == tag)))))

#push-options "--z3rlimit 50"
let receive (#n:nat{fragment_size <= n}) (buf:array byte n) (c:connection{receiver c})
  :ST (option nat) (requires (fun h0          -> Set.disjoint (connection_footprint c) (array_footprint buf)))
                 (ensures  (fun h0 r_opt h1 -> match r_opt with
					    | None   -> h0 == h1
					    | Some r ->
					      h0 `live_connection` c   /\
					      h1 `live_connection` c   /\
					      modifies_r c buf h0 h1       /\
					      disjoint_siblings_remain_same buf h0 h1 /\
					      r <= fragment_size            /\
					      all_init_i_j buf 0 r         /\
					      ctr c h1 = ctr c h0 + 1      /\
					      ctr c h0 < length (log c h0) /\
                                              log c h0 == log c h1 /\
					      (forall (i:nat). i < r ==> Some? (Seq.index (as_seq buf h1) i)) /\
					      Seq.index (log c h0) (ctr c h0) == as_initialized_subseq buf h1 0 r))
  = let h0 = ST.get () in
    let R rand es_ref ctr_ref = c in

    Set.lemma_disjoint_subset (connection_footprint c) (array_footprint buf) (Set.singleton (addr_of ctr_ref));

    recall_connection_liveness c;

    match network_receive c with
    | None               -> None
    | Some (cipher, tag) ->
      let i0 = ST.read ctr_ref in

      if verify c cipher tag i0 then
        let msg = xor cipher (rand i0) in
        let len, m = unpad msg in

	lemma_pad_unpad ();
        assert (m == Seq.index (log c h0) (ctr c h0));
        gst_witness (counter_pred (i0 + 1) es_ref);
        recall_contains buf;
        ST.write ctr_ref (i0 + 1);
        let h1 = ST.get () in
        lemma_disjoint_sibling_remain_same_for_unrelated_mods buf (Set.singleton (addr_of (ctr_ref))) h0 h1;
        fill buf m;
        let h2 = ST.get () in
        lemma_disjoint_sibling_remain_same_transitive buf h0 h1 h2;
        Some len
      else
        None
#pop-options

(***** sender and receiver *****)

let lemma_is_prefix_of_slice
  (#a:Type0) (s1:seq a) (s2:seq a{s1 `is_prefix_of` s2}) (i:nat) (j:nat{j >= i /\ j <= Seq.length s1})
  :Lemma (requires True)
         (ensures  (Seq.slice s1 i j == Seq.slice s2 i j))
	 [SMTPat (s1 `is_prefix_of` s2); SMTPat (Seq.slice s1 i j); SMTPat (Seq.slice s2 i j)]
  = ArrayUtils.lemma_is_prefix_of_slice s1 s2 i j

(*****)

(*
//  * assuming a flattening function that flattens a sequence of messages into sequence of bytes
//  * and a couple of associated lemmas
//  *)
assume val flatten (s:seq message) :Tot (seq byte)

assume val lemma_flatten_snoc (s:seq message) (m:message)
  :Lemma (requires True)
         (ensures  (flatten (snoc s m) == append (flatten s) m))

assume val flatten_empty (u:unit) : Lemma (flatten Seq.empty == Seq.empty)

(*****)

let sent_bytes' (file:seq byte) (c:connection) (from:nat) (to:nat{from <= to}) :heap_predicate
  = fun h -> h `live_connection` c /\ 
          (let log   = log c h in
           to <= Seq.length log /\ 
	   file == flatten (Seq.slice log from to))

let sent_bytes (file:seq byte) (c:connection) (from:nat) (to:nat{from <= to}) :(p:heap_predicate{stable p})
  = sent_bytes' file c from to

let sent (file:seq byte) (c:connection) =
  exists (from:nat) (to:nat{from <= to}). witnessed (sent_bytes file c from to)

#set-options "--z3rlimit 20"
let iarray_as_seq (#a:Type) (#n:nat) (x:iarray a n) : ST (seq a) 
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->  
              h0==h1 /\
              (forall (k:nat). k < n ==> Some? (Seq.index (as_seq x h0) k)) /\
              s == as_initialized_subseq x h0 0 n                    /\
	      s == as_initialized_seq x h0))
  = read_subseq_i_j x 0 n           

let fully_initialized_in #a #n (x:array a n) (h:heap) = 
  h `contains_array` x /\
  (forall (k:nat). k < n ==> Some? (Seq.index (as_seq x h) k))

let subseq_suffix #a #n (f:iarray a n) (pos:nat) (until:nat{pos+until <= n}) 
    (h:heap{f `fully_initialized_in` h})
  : Lemma  (as_initialized_subseq (suffix f pos) h 0 until ==
            as_initialized_subseq f h pos (pos + until))
  = assert (as_initialized_subseq (suffix f pos) h 0 until `Seq.equal`
            as_initialized_subseq f h pos (pos + until))        

let slice_snoc #a (s:seq a) (x:a) (from:nat) (to:nat{from<=to /\ to<=Seq.length s})
  : Lemma (slice s from to == slice (snoc s x) from to)
  = assert (slice s from to `Seq.equal` slice (snoc s x) from to)

let slice_snoc2 #a (s:seq a) (x:a) (from:nat{from <= Seq.length s})
  : Lemma (slice (snoc s x) from (Seq.length s + 1) == snoc (slice s from (Seq.length s)) x)
  = assert (slice (snoc s x) from (Seq.length s + 1) `Seq.equal` snoc (slice s from (Seq.length s)) x)

#push-options "--z3rlimit 100"
let append_subseq #a #n (f:iarray a n) (pos:nat) (sent:nat{pos + sent <= n}) (h:heap{f `fully_initialized_in` h})
    : Lemma (let f0 = as_initialized_subseq f h 0 pos in
             let f1 = as_initialized_subseq f h 0 (pos + sent) in
             let sub_file = suffix f pos in
             let sent_frag = as_initialized_subseq sub_file h 0 sent in
             f1 == append f0 sent_frag)
    = let f0 = as_initialized_subseq f h 0 pos in
      let f1 = as_initialized_subseq f h 0 (pos + sent) in
      let sub_file = suffix f pos in
      let sent_frag = as_initialized_subseq sub_file h 0 sent in

      let bs = as_seq f h in
      let bss = as_seq sub_file h in
      let sbs = ArrayUtils.get_some_equivalent bs in

      assert (f0 == ArrayUtils.get_some_equivalent (Seq.slice bs 0 pos));
      assert (f1 == ArrayUtils.get_some_equivalent (Seq.slice bs 0 (pos + sent)));
      assert (sent_frag == ArrayUtils.get_some_equivalent (Seq.slice bss 0 sent));
      assert (bss == Seq.slice bs pos n);
      assert (Seq.equal (Seq.slice bss 0 sent) (Seq.slice bs pos (pos + sent)));
      assert (sent_frag == ArrayUtils.get_some_equivalent (Seq.slice bs pos (pos + sent)));

      assert (f0 == Seq.slice sbs 0 pos);
      assert (f1 == Seq.slice sbs 0 (pos + sent));
      assert (sent_frag == Seq.slice sbs pos (pos + sent));
      lemma_seq_append_unstable sbs f0 sent_frag f1 pos sent
#pop-options

let lemma_sender_connection_ctr_equals_length_log
  (c:connection{sender c}) (h:heap{h `live_connection` c})
  :Lemma (ctr c h == Seq.length (log c h))
  = ()

#push-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"
val send_aux 
          (#n:nat) 
          (file:iarray byte n) 
          (c:connection{sender c /\ Set.disjoint (connection_footprint c) (array_footprint file)})
          (from:nat)
          (pos:nat{pos <= n})
      : ST unit 
             (requires (fun h0 ->
                      file `fully_initialized_in` h0 /\
                      h0 `live_connection` c /\
                      from <= ctr c h0 /\
                      sent_bytes (as_initialized_subseq file h0 0 pos) c from (ctr c h0) h0))
             (ensures  (fun h0 _ h1 -> 
                      modifies (connection_footprint c) h0 h1 /\
                      h1 `live_connection` c /\
                      from <= ctr c h1 /\
                      (forall (k:nat). k < n ==> Some? (Seq.index (as_seq file h0) k)) /\
                      sent_bytes (as_initialized_seq file h0) c from (ctr c h1) h1))
#push-options "--z3rlimit 500"
let rec send_aux #n file c from pos
      = if pos = n then ()
        else
          let sub_file = suffix file pos in
          lemma_all_init_i_j_sub file pos (n - pos);
       
          let h0 = ST.get () in
          let file_bytes0 = iarray_as_seq file in
          let log0 = log c h0 in
          let sent = send sub_file c in
          let h1 = ST.get () in
          let log1 = log c h1 in
          let file_bytes1 = iarray_as_seq file in          
          assert (file_bytes0 == file_bytes1);
          recall_contains file; //strange that this is needed
          assert (from <= ctr c h1);
          assert (file `fully_initialized_in` h1);
          assert (h1 `live_connection` c);
          let _ : unit = 
            let sent_frag = as_initialized_subseq sub_file h0 0 sent in
            let sent_frag' = as_initialized_subseq file h0 pos (pos + sent) in
            assert (log1 == snoc log0 sent_frag);
            subseq_suffix file pos sent h0; //sent_frag == sent_frag'
            slice_snoc log0 sent_frag from (ctr c h0); //slice log0 from (ctr c h0) == slice log1 from (ctr c h0)
            slice_snoc2 log0 sent_frag from; //Seq.slice log1 from (ctr c h1) == snoc (Seq.slice log0 from (ctr c h0)) sent_frag
            assert (ctr c h0 + 1 = ctr c h1);
	    lemma_sender_connection_ctr_equals_length_log c h0;
	    lemma_sender_connection_ctr_equals_length_log c h1;	    
	    assert (ctr c h0 = Seq.length log0);
            assert (ctr c h1 = Seq.length log1);
            let f0 = as_initialized_subseq file h1 0 pos in
            let f1 = as_initialized_subseq file h1 0 (pos + sent) in
            append_subseq file pos sent h1; //f1 == append f0 sent_frag
            assert (f1 == append f0 sent_frag);
            assert (f0 == flatten (Seq.slice log0 from (ctr c h0)));
            lemma_flatten_snoc (Seq.slice log0 from (ctr c h0)) sent_frag;
            assert (f1 == flatten (Seq.slice log1 from (ctr c h1)));
            assert (sent_bytes f1 c from (ctr c h1) h1) 
         in
         send_aux file c from (pos + sent)
#pop-options
let send_file (#n:nat) (file:iarray byte n) (c:connection{sender c /\ Set.disjoint (connection_footprint c) (array_footprint file)})
  : ST unit 
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 ->
                      modifies (connection_footprint c) h0 h1 /\
                      h1 `live_connection` c /\
                      (forall (k:nat). k < n ==> Some? (Seq.index (as_seq file h0) k)) /\
                      sent (as_initialized_seq file h0) c))
  = let h0 = ST.get () in
    recall_all_init file;
    recall_contains file;
    recall_connection_liveness c;
    let file_bytes0 = iarray_as_seq file in
    let from = ctr c h0 in
    assert (Seq.equal (as_initialized_subseq file h0 0 0) Seq.empty);
    flatten_empty();
    assert (Seq.equal (flatten (Seq.slice (log c h0) from from)) Seq.empty);
    send_aux file c from 0;
    let h1 = ST.get () in
    let file_bytes1 = iarray_as_seq file in
    assert (file_bytes0 == file_bytes1);
    gst_witness (sent_bytes file_bytes0 c from (ctr c h1));
    assert (sent file_bytes0 c)

let received (#n:nat) (file:iarray byte n) (c:connection) (h:heap) =
    file `fully_initialized_in` h /\
    sent (as_initialized_seq file h) c

#push-options "--z3rlimit_factor 4"
let append_filled #a #n (f:array a n) (pos:nat) (next:nat{pos + next <= n}) (h:heap)
  : Lemma (let f0 = prefix f pos in
           let f1 = prefix f (pos + next) in
           f1 `fully_initialized_in` h ==> (
           let b0 = as_initialized_seq f0 h in
           let b1 = as_initialized_seq f1 h in
           let received_frag = as_initialized_subseq (suffix f pos) h 0 next in
           Seq.equal b1 (append b0 received_frag)))
   = ()            //TAKES A LONG TIME
#pop-options

let extend_initialization #a #n (f:array a n) (pos:nat) (next:nat{pos+next <= n}) (h:heap)
  : Lemma (requires (let f0 = prefix f pos in
                     let f_next = prefix (suffix f pos) next in
                     f0 `fully_initialized_in` h /\
                     f_next `fully_initialized_in` h))
          (ensures (prefix f (pos + next) `fully_initialized_in` h))
  = let f0 = as_seq (prefix f pos) h in
    let f_next = as_seq (prefix (suffix f pos) next) h in
    let f1 = as_seq (prefix f (pos + next)) h in
    let aux (i:nat{i < pos + next}) : Lemma (Some? (Seq.index (as_seq (prefix f (pos + next)) h) i)) =
        if i < pos then assert (Seq.index f1 i == Seq.index f0 i)
        else assert (Seq.index f1 i == Seq.index f_next (i - pos))
    in
    FStar.Classical.forall_intro aux

let receive_aux_post
          (#n:nat)
          (file:array byte n)
          (c:connection{receiver c /\ Set.disjoint (connection_footprint c) (array_footprint file)})
          (h_init:heap{h_init `live_connection` c})
          (from:nat{from = ctr c h_init})
          (pos:nat{fragment_size <= n - pos})
          (ropt:option (r:nat{r <= n}))
          (h1:heap{h1 `live_connection` c}) =
          match ropt with
          | None -> True
          | Some r ->
            let file_out = prefix file r in
            all_init_i_j file_out 0 r /\
            file_out `fully_initialized_in` h1 /\
            from <= ctr c h1 /\
            sent_bytes (as_initialized_seq file_out h1) c from (ctr c h1) h1
            
val receive_aux
          (#n:nat)
          (file:array byte n)
          (c:connection{receiver c /\ Set.disjoint (connection_footprint c) (array_footprint file)})
          (h_init:heap{h_init `live_connection` c})
          (from:nat{from = ctr c h_init})
          (pos:nat{fragment_size <= n - pos})
    : ST (option (r:nat{r <= n}))
        (requires (fun h0 ->
              let file_in = prefix file pos in
              all_init_i_j file_in 0 pos /\
              file_in `fully_initialized_in` h0 /\
              h0 `live_connection` c /\
              from <= ctr c h0 /\
              sent_bytes (as_initialized_seq file_in h0) c from (ctr c h0) h0))
        (ensures (fun h0 ropt h1 ->
                   modifies_r c file h0 h1 /\
                   h1 `live_connection` c /\
                   receive_aux_post #n file c h_init from pos ropt h1))

#push-options "--query_stats"
let rec receive_aux #n file c h_init from pos
   = let h0 = ST.get() in
     let filled0 = prefix file pos in
     let filled_bytes0 = iarray_as_seq filled0 in
     let sub_file = suffix file pos in
     lemma_sub_footprint file pos (n - pos);
     assert (array_footprint sub_file == array_footprint file);
     match receive sub_file c with
       | None -> None
       | Some k ->
         let h1 = ST.get () in
         let filled_bytes0' = iarray_as_seq filled0 in
         lemma_disjoint_sibling_suffix_prefix file pos;
         assume (filled_bytes0 == filled_bytes0');
         let filled = prefix file (pos + k) in
         recall_all_init_i_j sub_file 0 k;
         recall_contains filled;
         extend_initialization file pos k h1;
         witness_all_init filled;
         let filled_bytes1 = iarray_as_seq filled in
         let received_frag = read_subseq_i_j sub_file 0 k in
         let h2 = ST.get () in
         assert (h2 == h1);
         assert (log c h0 == log c h1);
         assert (sent_bytes filled_bytes0 c from (ctr c h0) h0);
         assert (filled_bytes0 == flatten (Seq.slice (log c h0) from (ctr c h0)));
         append_filled file pos k h1; //(filled_bytes1 == append filled_bytes0 received_frag);
         assert (Seq.index (log c h0) (ctr c h0) == received_frag);
         lemma_flatten_snoc (Seq.slice (log c h0) from (ctr c h0)) received_frag;
         assert (filled_bytes1 == flatten (Seq.slice (log c h0) from (ctr c h1)));
         assert (sent_bytes filled_bytes1 c from (ctr c h1) h1);
         if k < fragment_size 
         || pos + k = n
         then (Some (pos + k))
         else if pos + k + fragment_size <= n
         then (let res = receive_aux file c h_init from (pos + k) in
               let h_post = ST.get () in
               assert (h_post `live_connection` c);
               assert (modifies_r c file h1 h_post); //from receive_aux
               assert (modifies_r c sub_file h0 h1); // from receive
               assert (modifies_r c file h0 h1); //weaken
               assert (modifies_r c file h0 h_post); //transitivity
               assert (receive_aux_post #n file c h_init from pos res h_post);
               assert (modifies_r c file h0 h_post /\
                       h_post `live_connection` c /\
                       receive_aux_post #n file c h_init from pos res h_post);
               res)
         else None

val receive_file (#n:nat{fragment_size <= n})
            (file:array byte n)
            (c:connection{receiver c /\ Set.disjoint (connection_footprint c) (array_footprint file)})
    : ST (option nat)
    (requires (fun h -> True))
    (ensures (fun h0 ropt h1 -> 
                modifies_r c file h0 h1 /\
                (match ropt with 
                 | None -> True 
                 | Some r ->
                   r <= n /\
                   all_init_i_j (prefix file r) 0 r /\
                   received (prefix file r) c h1)))
let receive_file #n file c = 
  let h_init = ST.get () in
  recall_contains file;
  recall_connection_liveness c;
  let R _ es ctr_ref = c in
  let from = !ctr_ref in 
  gst_recall (counter_pred from es);
  assert (from <= Seq.length (log c h_init));
  let file_in = prefix file 0 in
  let file_bytes0 = iarray_as_seq file_in in
  flatten_empty();
  assert (Seq.equal (flatten (Seq.slice (log c h_init) from from)) file_bytes0);
  match receive_aux #n file c h_init from 0 with
  | None -> None
  | Some r -> 
    let file_bytes1 = iarray_as_seq (prefix file r) in
    let h1 = ST.get() in
    gst_witness (sent_bytes file_bytes1 c from (ctr c h1));
    assert (sent file_bytes1 c);
    Some r

(* seq of tags sent so far on this connection *)
let tags (c:connection) (h:heap) :GTot (seq (seq byte)) =
  ArrayUtils.seq_map E?.tag (sel h (entries_of c))

#reset-options "--z3rlimit 100"
let lemma_partial_length_hiding
  (#n:nat) (#m:nat)
  (c0:connection{sender c0}) (c1:connection{sender c1})
  (h:heap{h `live_connection` c0 /\ h `live_connection` c1})
  (file0:iarray byte n) (file1:iarray byte m)
  (from:nat) (to:nat{from <= to /\ to <= Seq.length (log c0 h) /\ to <= Seq.length (log c1 h)})
  :Lemma (requires (let S rand0 _ = c0 in
                    let S rand1 _ = c1 in
	            (file0 `fully_initialized_in` h /\
	             file1 `fully_initialized_in` h /\
	             (let f0 = as_initialized_seq file0 h in
	              let f1 = as_initialized_seq file1 h in
	              sent_bytes f0 c0 from to h /\
	              sent_bytes f1 c1 from to h /\
	              (forall (i:nat). (i >= from /\ i < to) ==>
		                 xor (pad (Seq.index (log c0 h) i)) (rand0 i) ==
	                         xor (pad (Seq.index (log c1 h) i)) (rand1 i))))))
	 (ensures  (forall (i:nat). (i >= from /\ i < to) ==> (Seq.index (ciphers c0 h) i == Seq.index (ciphers c1 h) i) /\
	                                              Seq.index (tags c0 h) i == Seq.index (tags c1 h) i))
  = let S rand0 _ = c0 in
    let S rand1 _ = c1 in
    let ciphers0 = ciphers c0 h in
    let ciphers1 = ciphers c1 h in
    let tags0 = tags c0 h in
    let tags1 = tags c1 h in
    assert (forall (i:nat). (i >= from /\ i < to) ==> Seq.index ciphers0 i == xor (pad (Seq.index (log c0 h) i)) (rand0 i));
    assert (forall (i:nat). (i >= from /\ i < to) ==> Seq.index ciphers1 i == xor (pad (Seq.index (log c1 h) i)) (rand1 i));
    assert (forall (i:nat). (i >= from /\ i < to) ==> Seq.index tags0 i == mac (Seq.index ciphers0 i) i);
    assert (forall (i:nat). (i >= from /\ i < to) ==> Seq.index tags1 i == mac (Seq.index ciphers1 i) i)
