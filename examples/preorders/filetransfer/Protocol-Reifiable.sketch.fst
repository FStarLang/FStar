module Protocol

open FStar.Seq

open FStar.Preorder
open FStar.Heap
open FStar.ST //we should use the DM4F version of FStar.ST

(*** SOME INFRASTRUCTURE FOR 
     COMBINING DM4F WITH PREORDERS ***)
     
/// In a separate module FStar.Preorders.DM4F.ST

//1. assume a ghost flag; 
//   mark it GTot to ensure that it can't influence the computational behavior
assume val abstractST: unit -> GTot bool

//2. provide a guarded version of the reify (and reflect) operators
//Although we won't enforce it, promise to use only reify_wrapper in clients
val reify_wrapper: f:(unit -> ST a pre post){not (abstractST ())} 
                 -> (h0:heap -> Pure (a * heap) (pre h0) (fun (x, h1) -> post h0 x h1))
let reify_wrapper f h = reify (f ()) h
////////////////////////////////////////////////////////////////////////////////

//3. Guard witness and recall
/// I think these types of witness and recall are not exactly as
/// formalized But, treating witness and recall as identities with
/// trivial pre/post when abstractST=false is very convenient for
/// writing specs below. Search for "NS:snap" for an example.
val witness : #a:Type -> #p:preorder a -> r:mref a p{stable r p} -> ST unit 
  (requires (fun h -> abstractST() ==> p h))
  (ensures (fun h0 _ h1 -> h0==h1 /\ (abstractST() ==> p h1)))
val recall : p:(heap -> Type) -> ST unit 
  (requires (fun h -> abstractST() ==> witnessed p))
  (ensures (fun h0 _ h1 -> h0==h1 /\ (abstractST() ==> p h1)))

//4. With this version of recall, the type of (!) and (:=) will be slightly different

//assuming an mref is defined something like this, 
// i.e., we know that it's an address in the heap that contains a t-value with preorder p
type mref (t:Type) (p:preorder t) = 
  addr:nat{witnessed (contains_addr_at_type_and_preorder addr t p)}


//If there was some way to use sel instead of sel_tot in (!)
//then the spec wouldn't change ... which would be really nice. 
//Is it so bad to FStar.StrongExcludedmiddle in these functions?
//Anyway, in our current state, the change to the preconditions seems inevitable
let (!) (#a:Type) (#p:preorder a) (r:mref a p) : ST a
  (requires (fun h -> if abstractST () then True else h `contains` r)) //the precondition of (!) is no longer trivial
  (ensures (fun h0 v h1 -> h0==h1 /\ v = h1.[r]))
  = recall (contains_addr_at_type_and_preorder a p);
    assert (h `contains` r);
    let h = get() in sel_tot h r

//If there was some way to use upd instead of upd_tot in (:=)
//then the spec wouldn't change ... which would be really nice
let (:=) (#a:Type) (#p:preorder a) (r:mref a p) v : ST unit
  (requires (fun h -> p (sel h r) v /\ if abstractST () then True else h `contains` r)) //the precondition of (:=) includes containment in one case
  (ensures (fun h0 v h1 -> h1 == upd h0 r v))
  = recall (contains_addr_at_type_and_preorder a p);
    assert (h `contains` r);
    let h = get() in put (upd_tot h r v)

/// Now, for the rest of the program, I suggest just revising the
/// specs so that every function is well-typed for both cases of
/// abstractST(). Note, the program itself never contains occurences
/// of reify_wrapper within it, so it should make no strong
/// assumptions about abstractST(). We will finally use reify_wrapper
/// only on the "outside" when doing the proof of security, and in
/// that case we'll assume abstractST()=false.
///
/// This style of using a ghost boolean flag should work for this kind
/// of "reification for extrinsic proof" scenario.
///
/// However, it does not appear to be sufficient for the other kind of
/// example that Danel has been suggesting, where we build a program
/// (e1; e2; e3), and e2 does not respect the abstraction and uses a
/// reflect restoring the preorder only in a big step. That kind of
/// example really does seem to need support for indexed effects etc.

/// Anyway, we can say in the paper that the full implementation of
/// the system formalized in S4 is still underway, in particular,
/// we're still implementing indexed effects. But, that extrinsic
/// reification examples are encodeable without indexing (which is
/// what we used for the file-transfer example).

/// As for how to revise the specs in the program below, I'm thinking
/// that we should prove the bare minimum needed in the case where
/// abstractST()=false. For example, we should only strengthen
/// preconditions as much as needed to ensure that the uses of (!) and
/// (:=) still typecheck under their revised specs above. Search for
/// "NS" below to see some suggested spec revisions.

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

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

//NS:snap
//Here, i'm relying on recall and witness having trivial preconditions
//when (abstractST=false)
//Otherwise, the precondition of snap would basically have to include
//(not (abstractST()) ==> h `contains` ctr_ref /\ h `contains` msgs_ref)
//Which isn't the end of the world to include, but it's a bit painful
let snap (c:connection) :ST unit (requires (fun _ -> True))
                                 (ensures  (fun h0 _ h1 -> 
                                           //NS: added the guard here
                                           (abstractST() ==> (witnessed (counter_pred c h0) /\
				                              witnessed (log_pred c h0)))   /\
					   h0 == h1))
  = let h0 = ST.get () in
    let C _ ctr_ref msgs_ref = c in
    recall ctr_ref;
    recall msgs_ref;
    gst_witness (counter_pred c h0);
    gst_witness (log_pred c h0)

(* network send is called once log had been appended to etc. *)
assume val network_send
  (c:connection) (f:fragment)
  :ST unit (requires (fun h0 -> sender_connection_inv c h0 /\ ctr c h0 >= 1 /\
                             f == index (raw c h0) (ctr c h0 - 1)))
           (ensures  (fun h0 _ h1 -> h0 == h1))

(* type of the buffer and sender and receiver operate on *)
type iarray (n:nat) (a:Type) :Type //

(* these probably need some contains precondition? *)
assume val as_seq_ghost:
  #n:nat -> #a:Type -> x:iarray n a -> i:nat -> j:nat{j >= i /\ j <= n} -> h:heap{(*NS: yes, we need an h `contains` x *)}
  -> GTot (s:seq a{length s = j - i}) //NS:in the paper, these return a `seq (option a)`; if you want this return type then we also need an `all_init x h` preconditions


assume val as_seq:
  #n:nat -> #a:Type -> arr:iarray n a -> i:nat -> j:nat{j >= i /\ j <= n}
  -> ST (s:seq a{length s = j - i})
       (requires (fun h0 -> (*NS:*) (if abstractST () then True else all_init arr h0)))
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
  :ST nat (requires (fun h0 -> (*NS:*) 
                     if abstractST () 
                     then True 
                     else (h0 `contains` C.ctr c /\
                           h0 `contains` C.msgs c /\
                           all_init buf h0))) (* NS: this kind of precondition strengthening is a drag ... *)
        (ensures  (fun h0 sent h1 -> 
                     modifies_s c h0 h1            /\
	             (abstractST() ==> 
                                     sender_connection_inv c h1 /\ 
	                             sent <= min n fragment_size  /\
				     ctr c h1 = ctr c h0 + 1     /\
                                     log c h1 == snoc (log c h0)
				                      (append (as_seq_ghost buf 0 sent h0)
						              (zeroes (fragment_size - sent))))))
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
  :ST (option nat) (requires (fun h0          -> (*NS:*)if abstractST() then True else (h0 `contains` C.ctr c /\ h0 `contains` C.msgs c)))
                 (ensures  (fun h0 r_opt h1 -> match r_opt with
					    | None   -> h0 == h1
					    | Some r ->
					      modifies_r c buf h0 h1       /\
                                              (* NS: *)
                                              (abstractST () ==>
      					        receiver_connection_inv c h1 /\
					        r <= fragment_size            /\
					        all_init buf 0 r             /\
					        ctr c h1 = ctr c h0 + 1      /\
					        ctr c h0 < length (log c h0) /\
					        index (log c h0) (ctr c h0) ==
					        append (as_seq_ghost_a buf 0 r h1) (zeroes (fragment_size - r)))))
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

