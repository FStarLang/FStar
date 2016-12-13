module Crypto.AEAD.Invariant
// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.AEAD.Encoding 
open Crypto.Symmetric.PRF

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

//16-09-18 where is it in the libraries??
let min (a:u32) (b:u32) = if a <=^ b then a else b
let minNat (a:nat) (b:nat) : nat = if a <= b then a else b

type eternal_region = rgn:HH.rid {HS.is_eternal_region rgn}

let prf_table (r:rgn) (i:id) = Seq.seq (PRF.entry r i)

(* An idealization flag controlling per-id authentication alone *)
let safeMac (i:id) = safeHS i && mac1 i

(*** COUNTERS AND LENGTHS ***)
let u (n:FStar.UInt.uint_t 32) = uint_to_t n

(* The ctr value associated with the first otp block *)
let otp_offset (i:id) = ctr_0 i +^ 1ul

let aadlen = aadlen_32

let maxplain (i:id) = pow2 14 // for instance

let num_blocks_for_len (i:id) (l:nat) : Tot nat =
  let bl = v (Cipher.( blocklen (cipherAlg_of_id i))) in
  (l + bl - 1) / bl

(*+ safelen: The length of the plaintext is not too large **)
let safelen (i:id)
	    (remaining_len:nat)  //the length of plaintext left to be encrypted;
	    (next_block_index:UInt32.t) //the counter for encrypting the next block of plaintext
  =
  let open FStar.Mul in
  PRF.ctr_0 i <^ next_block_index &&                  //next_block_index is strictly greater than the mac domain position
  next_block_index <=^ PRF.maxCtr i &&               //and less then the max counter
  (let block_length = v (Cipher.(blocklen (cipherAlg_of_id i))) in
   let len_all_blocks_so_far = v (next_block_index -^ PRF.ctr_0 i -^ 1ul) * block_length in
   let max_len_for_remaining_blocks = v (PRF.maxCtr i -^ next_block_index) * block_length in
   remaining_len = 0 ||                               //no more text left to encrypt, or
   (remaining_len + len_all_blocks_so_far <= maxplain i &&
    remaining_len <= max_len_for_remaining_blocks))

(*+ remaining_len_ok: 
      Given a plaintext of length len, with remaining_len left to encrypt,
      the current_block_index accurately characterizes the number of blocks 
      already encrypted **)
let remaining_len_ok (#i:id) (current_block_index:PRF.domain i) (len:u32) (remaining_len:u32) =
  PRF.ctr_0 i <^ current_block_index.ctr &&
  safelen i (v remaining_len) current_block_index.ctr &&
  remaining_len <=^ len &&
  len <> 0ul &&
  safelen i (v len) (otp_offset i) &&
  (let completed_len = v len - v remaining_len in
   let n_blocks = v current_block_index.ctr - v (otp_offset i) in
   if remaining_len = 0ul then
      n_blocks = num_blocks_for_len i (v len)
   else completed_len = FStar.Mul.(n_blocks * v (PRF.blocklen i)))

(*** THE TYPE OF AEAD KEYS ***)
noeq type aead_entry (i:id) =
  | AEADEntry:
      nonce:Cipher.iv (alg i) ->
      ad:adata ->
      l:plainLen ->
      p:plain i l ->
      c:cipher i (Seq.length (as_bytes p)) ->
      aead_entry i

let aead_entries i = Seq.seq (aead_entry i)

//TODO: move this to HyperStack
let rref (r:rid) (a:Type) = x:HS.ref a {HS.frameOf x == r}

(*+ aead_log: The type of the conditional, ideal aead_log **)
let aead_log (r:rgn) (i:id) =
  if safeMac i 
  then rref r (aead_entries i)
  else unit

(*+ aead_log_as_ref: A coercion from a conditional log to the ideal case *)
let aead_log_as_ref (#r:rgn) (#i:id) (x:aead_log r i{safeMac i}) 
  : rref r (aead_entries i)
  = x

(*+ aead_state: the type of aead keys, also encapsulating their ideal state *)
noeq type aead_state (i:id) (rw:rw) =
  | AEADState:
      #log_region: rgn -> // this is the *writer* region; the reader allocates nothing
      log: aead_log log_region i ->
      prf: PRF.state i {prf.rgn == log_region /\ //TODO: PRF state will move to the TLS region
		       (safeMac i ==> ~(aead_log_as_ref log === PRF.itable i prf)) } ->
      ak: CMA.akey prf.mac_rgn i (* static, optional authentication key *) ->
      aead_state i rw

(*+ st_ilog: Projecting the log from an aead_state, in the ideal case *)
let st_ilog (#i:id) (#rw:rw) (x:aead_state i rw{safeMac i})
  : rref x.log_region (aead_entries i)
  = aead_log_as_ref x.log

(*** MAIN STATEFUL INVARIANT ***)

(*+ Some utilities for stating the invariant **)
noextract let is_aead_entry_nonce (#i:id) (n:Cipher.iv (alg i)) (e:aead_entry i) =
  e.nonce = n

noextract let find_aead_entry (#i:id) (n:Cipher.iv (alg i)) (entries:Seq.seq (aead_entry i))
  : option (aead_entry i)
  = SeqProperties.find_l (is_aead_entry_nonce n) entries

let fresh_nonce (#i:id) (n:Cipher.iv (alg i)) (entries:aead_entries i) =
    None? (find_aead_entry n entries)

let fresh_nonce_st (#i:id) (#rw:rw) (n:Cipher.iv (alg i)) (aead_st:aead_state i rw) (h:mem) = 
  safeMac i ==> 
  fresh_nonce n (HS.sel h aead_st.log)

let num_blocks_for_entry (#i:id) (e:aead_entry i) : Tot nat =
  let AEADEntry nonce ad l plain cipher_tagged = e in
  num_blocks_for_len i l

let encode_ad_cipher (i:id) (ad:adata) (l:plainLen{safelen i l (PRF.ctr_0 i +^ 1ul)}) (cipher:lbytes l) =
  encode_both i (FStar.UInt32.uint_to_t (Seq.length ad)) ad (FStar.UInt32.uint_to_t l) cipher

(*+ counterblocks:
         A sequence of OTP entries for the PRF table
	 corresponding to the fragmentation of the 
	 plain and cipher into encrypted blocks, 
	 starting from position x, until to_pos **)
val counterblocks:
  i:id{safeId i} ->
  mac_rgn:eternal_region ->
  x:PRF.domain i{PRF.ctr_0 i <^ PRF.(x.ctr)} ->
  l:nat ->
  from_pos:nat ->
  to_pos:nat{from_pos <= to_pos /\ to_pos <= l /\ safelen i (to_pos - from_pos) PRF.(x.ctr)} ->
  plain:Crypto.Plain.plain i l ->
  cipher:lbytes l ->
  Tot (prf_table mac_rgn i) // each entry e {PRF(e.x.id = x.iv /\ e.x.ctr >= ctr x)}
  (decreases (to_pos - from_pos))
let rec counterblocks i mac_rgn x l from_pos to_pos plain cipher =
  let blockl = v (Cipher.(blocklen (cipherAlg_of_id i))) in
  let remaining = to_pos - from_pos in
  if remaining = 0 then
    Seq.createEmpty
  else
    let l0 = minNat remaining blockl in
    let l_32 = UInt32.uint_to_t l0 in
    let plain_hd = Crypto.Plain.slice plain from_pos (from_pos + l0) in
    let cipher_hd = Seq.slice cipher from_pos (from_pos + l0) in
    //safeId i is needed here, to show that OTP is a suitable range
    //NB: cf issue: Separate integrity from confidentiality in AEAD (#153)
    //    this could account for both the cases of safe_mac/safeId here
    let block = PRF.Entry x (PRF.OTP l_32 plain_hd cipher_hd) in 
    let blocks = counterblocks i mac_rgn (PRF.incr i x) l (from_pos + l0) to_pos plain cipher in
    SeqProperties.cons block blocks

(*+ mac_is_set prf_table iv: 
        the mac entry in the prf_table, at location (iv, ctr_0 i)
	is set to the suitable encoded ad + cipher, tag      **)
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_is_set (#rgn:region) (#i:id)
	       (prf_table:prf_table rgn i{mac_log}) //the entire prf table
	       (iv:Cipher.iv (alg i))
	       (ad:adata)
	       (l:plainLen)
	       (cipher:lbytes l)
	       (tag:MAC.tag)
	       (h:mem) : GTot Type0
  = let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
    //the mac entry for this nonce in the prf table contains a mac'd ad+cipher
    (match PRF.find_mac prf_table dom_0 with
     | None -> False
     | Some mac_range ->
       let mac_st = CMA.ilog (CMA.State?.log mac_range) in
       m_contains mac_st h /\ (
       match m_sel h mac_st with
       | None           -> False
       | Some (msg,tag') ->
	 safelen i l (PRF.ctr_0 i +^ 1ul) /\
	 msg = encode_ad_cipher i ad l cipher /\
 	 tag = tag'))

(*+ prf_contains_all_otp_blocks:
        There are entries in the
	prf_table (order unspecified) for all the otp entries
	corresponding to the encrypted plain text
 **)
let prf_contains_all_otp_blocks 
      (#i:id) (#r:rid)
      (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
      (#len:nat)
      (from_pos:nat{from_pos <= len /\ safelen i (len - from_pos) PRF.(x.ctr)})
      (plain:plain i len)
      (cipher:lbytes len)
      (prf_table:prf_table r i)
   = let open FStar.SeqProperties in
     (safeId i ==> (
      let otp_blocks = counterblocks i r x len from_pos len plain cipher in
      (forall (prf_entry:PRF.entry r i).{:pattern (otp_blocks `contains` prf_entry)} 
       otp_blocks `contains` prf_entry ==>
       PRF.find prf_table prf_entry.x == Some prf_entry.range)))

(*+ refines_one_entry:
        Conceptually, read it as (prf_table `refines_one_entry` aead_entry)
	It states that there are entries in the prf_table (order unspecified)
	that contains the mac and otp entries corresponding to aead_entry
**)
let refines_one_entry (#rgn:region) (#i:id)
		      (prf_table:prf_table rgn i) //the entire prf table
		      (aead_entry:aead_entry i)   //a single aead_entry
		      (h:mem{safeId i})
 = let open FStar.SeqProperties in
   let AEADEntry iv ad l plain cipher_tagged = aead_entry in
   let b = num_blocks_for_entry aead_entry in //number of expected OTP blocks
   let total_blocks = b + 1 in //including the MAC block
   let cipher, tag = split cipher_tagged l in
   let dom_1:(PRF.domain i) = {iv=iv; ctr=PRF.ctr_0 i +^ 1ul} in
   safelen i l dom_1.ctr /\ //it's not too long
   //1. the mac entry for this nonce in the prf table contains a mac'd ad+cipher
   mac_is_set prf_table iv ad l cipher tag h /\
   //2. all the expected otp_blocks are in the table, in some order
   prf_contains_all_otp_blocks dom_1 0 plain cipher prf_table
   //NB: this does not forbid the prf_table from containing other OTP blocks with the same IV;
   //    not clear whether we need that

(*+ none_above x prf_table:
	no entry in the prf_table at ({iv=x.iv; ctr=i}) for any i >= x.ctr **)
let none_above (#r:region) (#i:id) (x:PRF.domain i) (prf_table:prf_table r i) =
    forall (y:PRF.domain i{y `PRF.above` x}).{:pattern (y `PRF.above` x) \/ (PRF.find prf_table y)} //Pattern added: 12/7
	PRF.find prf_table y == None

(*+ none_above_prf_st x prf_state h:
        A stateful variant of none_above, using the full prf_table in h **)
let none_above_prf_st (#i:id) (x:PRF.domain i) (st:PRF.state i) (h:mem) =
  prf i ==> 
    (let prf_table = HS.sel h (itable i st) in
     none_above x prf_table)

(*+ all_above x prf_blocks
	every entry in the prf_blocks is above x  ({iv=x.iv; ctr=i}) for any i >= x.ctr

	This is generally used for some sequence of prf entries,
	not the full prf table
**)
let all_above (#rgn:region) (#i:id) (x:PRF.domain i) (s:prf_table rgn i) =
  (forall (e:PRF.entry rgn i).{:pattern (s `SeqProperties.contains` e)}
     s `SeqProperties.contains` e ==> e.x `PRF.above` x)

(*+ unused_aead_iv_for_prf prf_table iv:
	the iv is either fresh, i.e., doesn't appear anywhere in the prf_table
	Or, it occurs there with an unused mac (e.g., decrypt allocated one early)
 **)
let unused_aead_iv_for_prf (#mac_rgn:region) (#i:id)
			   (prf_table:prf_table mac_rgn i) //the entire prf table
  			   (iv:Cipher.iv (alg i))
			   (h:mem{safeMac i}) : GTot Type0
  = let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
    none_above (PRF.incr i dom_0) prf_table /\ //There are no OTP entries for this IV at all
    (match PRF.find_mac prf_table dom_0 with
     | None           -> True //and no MAC entry either
     | Some mac_range -> CMA.mac_is_unset (i, iv) mac_rgn mac_range h) //Or, a mac exists, but it's not yet used

let aead_entries_are_refined (#rgn:region) (#i:id)
                             (prf_table: prf_table rgn i)
	                     (aead_entries:Seq.seq (aead_entry i))
	                     (h:mem) : GTot Type0 =
  let open FStar.SeqProperties in
  (safeId i ==> (forall (aead_entry:aead_entry i).{:pattern (aead_entries `contains` aead_entry)}
		   aead_entries `contains` aead_entry ==>
		   refines_one_entry prf_table aead_entry h))

let fresh_nonces_are_unused (#rgn:region) (#i:id)
                            (prf_table: prf_table rgn i)
	                    (aead_entries:Seq.seq (aead_entry i))
	                    (h:mem{safeMac i}) : GTot Type0 =
  let open FStar.SeqProperties in
  (forall (iv:Cipher.iv (alg i)).{:pattern (fresh_nonce iv aead_entries)}
     fresh_nonce iv aead_entries ==> 
     unused_aead_iv_for_prf prf_table iv h)

(*+ refines prf_table aead_entries h:
	THE MAIN CLAUSE OF THE STATEFUL INVARIANT:
	In state h, prf_table refines aead_entries
 **)
let refines (#rgn:region) (#i:id)
            (prf_table: prf_table rgn i)
	    (aead_entries:Seq.seq (aead_entry i))
	    (h:mem{safeMac i}) : GTot Type0 =
  aead_entries_are_refined prf_table aead_entries h /\
  fresh_nonces_are_unused  prf_table aead_entries h

(*+ aead_liveness:
	The aead_state and its regions etc. are live **)
let aead_liveness (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) : Type0 =
  HS.(h.h `Map.contains` st.prf.mac_rgn) /\        //contains the mac region
  (safeMac i ==> h `HS.contains` (st_ilog st)) /\  //contains the aead log
  (prf i ==> h `HS.contains` (itable i st.prf))   //contains the prf table


(*** inv st h:
       The final stateful invariant,
       refines and aead_state_live ***)
let inv (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) : Type0 =
  aead_liveness st h /\
  (safeMac i ==>
     (let prf_table = HS.sel h (itable i st.prf) in
      let aead_entries = HS.sel h st.log in
      refines prf_table aead_entries h))


(*** SEPARATION AND LIVENESS
     REQUIREMENTS OF THE INTERFACE ***)

module Plain = Crypto.Plain
(*+ enc_dec_separation:
	Calling AEAD.encrypt/decrypt requires this separation **)
let enc_dec_separation (#i:id) (#rw:rw) (st:aead_state i rw)
		       (#aadlen:nat) (aad: lbuffer aadlen)
		       (#plainlen:nat) (plain: plainBuffer i plainlen)
		       (#cipherlen: nat) (cipher:lbuffer cipherlen) =
    Buffer.disjoint aad cipher /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher /\
    HS.is_eternal_region st.log_region /\
    HS.is_eternal_region (Buffer.frameOf cipher) /\ // why?
    HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\ //why?
    HS.is_eternal_region (Buffer.frameOf aad) /\ //why?
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
    HH.disjoint (Buffer.frameOf cipher) st.log_region /\
    HH.disjoint (Buffer.frameOf aad) st.log_region /\
    st.log_region <> HH.root /\
    Buffer.frameOf cipher <> HH.root /\
    Buffer.frameOf aad <> HH.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HH.root

(*+ enc_dec_liveness:
	Calling AEAD.encrypt/decrypt requires and ensures this liveness **)
let enc_dec_liveness (#i:id) (#rw:rw) (st:aead_state i rw)
		  (#aadlen:nat) (aad: lbuffer aadlen)
		  (#plainlen:nat) (plain: plainBuffer i plainlen)
		  (#cipherlen: nat) (cipher:lbuffer cipherlen) (h:mem) =
    let open HS in
    Buffer.live h aad /\
    Buffer.live h cipher /\
    Plain.live h plain /\
    st.log_region `is_in` h.h

(*** SOME BASIC LEMMAS USED 
     THROUGHOUT Crypto.AEAD.* ***)
let incr_remaining_len_ok (#i:id) (x:PRF.domain i) (len:u32) (remaining_len:u32)
    : Lemma (let l = min remaining_len (PRF.blocklen i) in
	     remaining_len_ok x len remaining_len /\
             remaining_len <> 0ul ==>
	     remaining_len_ok (PRF.incr i x) len (remaining_len -^ l))
    = ()

let init_remaining_len_ok (#i:id) (x:PRF.domain i{PRF.ctr_0 i +^ 1ul = x.ctr})
			  (len:u32{len <> 0ul /\ safelen i (v len) x.ctr})
    : Lemma (remaining_len_ok x len len)
    = ()

(*+ Framing lemmas for clauses of the main invariant **)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_refines_one_entry (#i:id) (#mac_rgn:region) 
			    (h:mem) (h':mem) 
			    (blocks:prf_table mac_rgn i)
			    (e:aead_entry i{safeId i}) //NB: moving the refinement earlier causes typing problems in frame_refines below
   : Lemma (requires (let open HS in
		      refines_one_entry blocks e h /\			    
		      HH.modifies_rref mac_rgn TSet.empty h.h h'.h /\
		      live_region h' mac_rgn))
	   (ensures  refines_one_entry blocks e h')
   = ()

let frame_unused_aead_iv_for_prf (#mac_rgn:region) (#i:id) (h0:mem{safeMac i}) (h1:mem)
				 (prf_table:prf_table mac_rgn i)
				 (iv:Cipher.iv (alg i))
  : Lemma (requires (let open HS in
		     unused_aead_iv_for_prf prf_table iv h0        /\
                     HH.modifies_rref mac_rgn TSet.empty h0.h h1.h /\
		     live_region h1 mac_rgn))
	  (ensures  unused_aead_iv_for_prf prf_table iv h1)
  = ()

let frame_refines (i:id{safeMac i}) (mac_rgn:region) 
		  (blocks:prf_table mac_rgn i)
		  (entries:aead_entries i)
		  (h:mem) (h':mem)
   : Lemma (requires (let open HS in 
		      refines blocks entries h                     /\
   		      HH.modifies_rref mac_rgn TSet.empty h.h h'.h /\
		      HS.live_region h' mac_rgn))
	   (ensures  refines blocks entries h')
   = let open FStar.Classical in
     forall_intro (move_requires (frame_unused_aead_iv_for_prf h h' blocks));
     if safeId i then forall_intro (move_requires (frame_refines_one_entry h h' blocks))

let frame_inv_push (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) (h1:mem)
   : Lemma (requires (inv st h /\ 
		      HS.fresh_frame h h1))
	   (ensures  (inv st h1))
   = if safeMac i
     then frame_refines i st.prf.mac_rgn (HS.sel h (PRF.itable i st.prf)) (HS.sel h st.log) h h1

let weaken_all_above (#rgn:region) (#i:id) (s:Seq.seq (PRF.entry rgn i)) 
		    (x:PRF.domain i) (y:PRF.domain i{y `above` x})
    : Lemma (all_above y s ==> all_above x s)
    = ()

(*+ counterblocks_emp:
	proves that counterblocks on a zero range is the empty sequence
 **)
#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let counterblocks_emp   (i:id)
			(rgn:region)
			(x:PRF.domain i{ctr_0 i <^ PRF.(x.ctr) })
			(l:nat)
			(to_pos:nat{to_pos <= l /\ safelen i 0 PRF.(x.ctr)})
			(plain:Plain.plain i l)
			(cipher:lbytes l)
   : Lemma (safeId i ==> counterblocks i rgn x l to_pos to_pos plain cipher == Seq.createEmpty)
   = ()

(*+ Lemmas about searching for entries in prf_blocks **)
let find_append (#i:id) (#r:rid) (d:domain i) (s1:prf_table r i) (s2:prf_table r i)
   : Lemma (requires (None? (find s1 d)))
           (ensures (find (Seq.append s1 s2) d == find s2 d))
   = SeqProperties.find_append_none s1 s2 (is_entry_domain d)

#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 2 --max_fuel 2"
let find_singleton (#rgn:region) (#i:id) (e:PRF.entry rgn i) (x:PRF.domain i) 
    : Lemma (if is_entry_domain x e then PRF.find (Seq.create 1 e) x == Some e.range
	     else PRF.find (Seq.create 1 e) x == None)
    = ()	     

let lemma_prf_find_append_some
  (#r:region)
  (#i:id)
  (table:prf_table r i)
  (blocks:prf_table r i)
  (x:PRF.domain i) 
  : Lemma
    (requires (Some? (PRF.find table x)))
    (ensures  (PRF.find (Seq.append table blocks) x == PRF.find table x))
  = SeqProperties.find_append_some table blocks (is_entry_domain x)

let lemma_prf_find_append_some_forall
  (#r:region)
  (#i:id)
  (table:prf_table r i)
  (blocks:prf_table r i) : 
  Lemma 
    (ensures 
	(forall (x:PRF.domain i).{:pattern (PRF.find (Seq.append table blocks) x) }
	   Some? (PRF.find table x) ==>
	   PRF.find (Seq.append table blocks) x == PRF.find table x))
 = let open FStar.Classical in
   forall_intro (move_requires (lemma_prf_find_append_some #r #i table blocks))

(*
 * refines_one_entry framing lemma for append to the PRF blocks
 *)
let frame_refines_one_entry_append
  (#r:region)
  (#i:id)
  (table:prf_table r i)
  (h:mem)
  (blocks:prf_table r i)
  (aead_ent: aead_entry i{safeId i}) 
  : Lemma
      (requires (refines_one_entry table aead_ent h))
      (ensures  (refines_one_entry (Seq.append table blocks) aead_ent h))
  = lemma_prf_find_append_some_forall table blocks; admit() //NS: doesn't go through

(*
 * aead_entries_are_refined framing lemma for append to the PRF blocks
 *)
let frame_refines_entries_prf_append
  (#r:region)
  (#i:id)
  (table:prf_table r i)
  (entries:aead_entries i)
  (h:mem)
  (blocks:prf_table r i) 
  : Lemma
      (requires (aead_entries_are_refined table entries h))
      (ensures  (aead_entries_are_refined (Seq.append table blocks) entries h))
  = let open FStar.Classical in
    if safeId i 
    then forall_intro (move_requires (frame_refines_one_entry_append table h blocks))


(*
 * aead_entries_are_refined framing lemma for no changes to heap in the mac_rgn
 *)
let frame_refines_entries_h (i:id{safeMac i}) (mac_rgn:region) 
		                 (blocks:prf_table mac_rgn i)
		                 (entries:aead_entries i)
		                 (h:mem) (h':mem)
   : Lemma (requires (let open HS in 
		      aead_entries_are_refined blocks entries h    /\
   		      HH.modifies_rref mac_rgn TSet.empty h.h h'.h /\
		      HS.live_region h' mac_rgn))
	   (ensures  aead_entries_are_refined blocks entries h')
   = let open FStar.Classical in
     forall_intro (move_requires (frame_unused_aead_iv_for_prf h h' blocks));
     if safeId i then forall_intro (move_requires (frame_refines_one_entry h h' blocks))

(*+ mac_is_used prf_table iv: 
	the mac entry for iv is present
	and the corresponding one-time mac has been used already
 **)	
let mac_is_used (#rgn:region) (#i:id)
	        (prf_table:prf_table rgn i) //the entire prf table
 	        (iv:Cipher.iv (alg i))
	        (h:mem) : GTot Type0
  = mac_log ==> (
    let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
    //the mac entry for this nonce in the prf table contains a mac that's already been used
    (match PRF.find_mac prf_table dom_0 with
     | None -> False
     | Some mac_range ->
       let mac_st = CMA.ilog (CMA.State?.log mac_range) in
       Some? (m_sel h mac_st)))

let find_refined_aead_entry
    (#i:id) (#r:rid)
    (n:Cipher.iv (alg i){safeId i})
    (aead_entries:aead_entries i)
    (prf_entries:prf_table r i)
    (h:mem)
  : Pure (aead_entry i)
         (requires (refines prf_entries aead_entries h /\
		    mac_is_used prf_entries n h))
	 (ensures (fun entry ->
		  entry.nonce = n /\
		  refines_one_entry prf_entries entry h /\
		  find_aead_entry n aead_entries == Some entry))
  = match find_aead_entry n aead_entries with
    | None -> 
      assert (fresh_nonce n aead_entries); 
      false_elim()
    | Some e -> 
      SeqProperties.lemma_find_l_contains (is_aead_entry_nonce n) aead_entries;
      e

(*** LEMMAS ABOUT counterblocks
	      AND prf_contains_all_otp_blocks ***)

(*+ counterblocks_snoc: 
        rewrite the indexed-based invocation of counterblocks into a 
	and inductive form based on snoc.
        Each recursive invocation effectively snoc's a PRF block **)
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
val counterblocks_snoc: #i:id{safeId i} -> (rgn:region) -> (x:domain i{ctr_0 i <^ x.ctr}) -> (k:nat{v x.ctr <= k}) ->
			 (len:nat{len <> 0 /\ safelen i len (ctr_0 i +^ 1ul)})  ->
			 (next:nat{0 < next /\ next <= v (PRF.blocklen i)}) ->
			 (completed_len:nat{ completed_len + next <= len /\ 
					   FStar.Mul.((k - v (otp_offset i)) * v (PRF.blocklen i) = completed_len)}) ->
			 (plain:Plain.plain i len) ->
			 (cipher:lbytes len) ->
     Lemma (requires True)
	   (ensures
	     (let open FStar.Mul in
	      let plain_last = Plain.slice plain completed_len (completed_len + next) in
	      let cipher_last = Seq.slice cipher completed_len (completed_len + next) in
	      let from = (v x.ctr - (v (otp_offset i))) * v (PRF.blocklen i) in
	      Seq.equal (counterblocks i rgn x len from (completed_len + next) plain cipher)
			(SeqProperties.snoc (counterblocks i rgn x len from completed_len plain cipher)
							   (PRF.Entry ({x with ctr=UInt32.uint_to_t k}) 
							              (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last)))))
	   (decreases (completed_len - v x.ctr))
#reset-options "--z3rlimit 400 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec counterblocks_snoc #i rgn x k len next completed_len plain cipher =
   let open FStar.Mul in
   let from_pos = (v x.ctr - (v (otp_offset i))) * v (PRF.blocklen i) in
   let to_pos = completed_len + next in
   if completed_len - from_pos = 0
   then counterblocks_emp i rgn (PRF.incr i x) len to_pos plain cipher
   else   let y = PRF.incr i x in
	  let remaining = to_pos - from_pos in 
	  let l0 = minNat remaining (v (PRF.blocklen i)) in
	  let plain_hd = Plain.slice plain from_pos (from_pos + l0) in
	  let cipher_hd = Seq.slice cipher from_pos (from_pos + l0) in
	  let plain_last = Plain.slice plain completed_len (completed_len + next) in
	  let cipher_last = Seq.slice cipher completed_len (completed_len + next) in
	  let head = PRF.Entry x (PRF.OTP (UInt32.uint_to_t l0) plain_hd cipher_hd) in
	  let recursive_call = counterblocks i rgn y len (from_pos + l0) to_pos plain cipher in
	  let middle = counterblocks i rgn y len (from_pos + l0) completed_len plain cipher in
	  let last_entry = PRF.Entry ({x with ctr=UInt32.uint_to_t k}) (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last) in
	  assert (counterblocks i rgn x len from_pos to_pos plain cipher ==
		  SeqProperties.cons head recursive_call);
	  counterblocks_snoc rgn y k len next completed_len plain cipher;
	  assert (recursive_call == SeqProperties.snoc middle last_entry);
          SeqProperties.lemma_cons_snoc head middle last_entry //REVIEW: THIS PROOF TAKES A WHILE ...optimize

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
(*+ counterblocks_slice: 
	counterblocks only depends on the fragment of plain and cipher
	accessible to it between from_pos and to_pos **)
val counterblocks_slice: #i:id{safeId i} -> 
			     (rgn:region) -> 
			     (x:domain i{ctr_0 i <^ x.ctr}) ->
			     (len:nat{len <> 0}) ->
			     (from_pos:nat) ->
			     (to_pos:nat{from_pos <= to_pos /\ to_pos <= len /\ safelen i (to_pos - from_pos) x.ctr}) ->
			     (plain:Plain.plain i len) ->
			     (cipher:lbytes len) ->
    Lemma (requires True)
	   (ensures
	     (Seq.equal (counterblocks i rgn x len from_pos to_pos plain cipher)
	 	        (counterblocks i rgn x (to_pos - from_pos) 0 (to_pos - from_pos)
					       (Plain.slice plain from_pos to_pos) 
 					       (Seq.slice cipher from_pos to_pos))))
           (decreases (to_pos - from_pos))						 
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec counterblocks_slice #i rgn x len from_pos to_pos plain cipher =
    (* The general proof idea:
       let from' = from + l
       cb from to p
       = slice p from from'          @ cb from' to p                           //unfolding
       =      ''      ''             @ cb 0 (to - from') (slice p from' to)    //IH1
       =      ''      ''             @ cb 0 (to - from') (slice (slice p from to) l (to - from)) //slice-slice-1
       =      ''      ''             @ cb l (to - from) (slice p from to)      //IH2 (backwards)
       = slice (slice p from to) 0 l @     ''                ''                //slice-slice-2
       = cb 0 (to - from) (slice p from to)                                    //folding
     *)
   let remaining = to_pos - from_pos in 
   if remaining = 0
   then ()
   else let l = minNat remaining (v (PRF.blocklen i)) in
        let y = PRF.incr i x in
	let from_pos' = from_pos + l in
	let ih1 = counterblocks_slice rgn y len from_pos' to_pos plain cipher in
  	let ih2 = counterblocks_slice rgn y (to_pos - from_pos) l (to_pos - from_pos) (Plain.slice plain from_pos to_pos) (Seq.slice cipher from_pos to_pos) in
	  //slice-slice-1
	  assert (Seq.equal (as_bytes #i #(to_pos - from_pos') (Plain.slice plain from_pos' to_pos))
			    (as_bytes #i #(to_pos - from_pos') (Plain.slice (Plain.slice plain from_pos to_pos) l (to_pos - from_pos))));
	  assert (Seq.equal (Seq.slice cipher from_pos' to_pos)
			    (Seq.slice (Seq.slice cipher from_pos to_pos) l (to_pos - from_pos)));
	  //slice-slice-2
          assert (Seq.equal (as_bytes #i #l (Plain.slice (Plain.slice plain from_pos to_pos) 0 l))
			    (as_bytes #i #l (Plain.slice plain from_pos from_pos')));
          assert (Seq.equal (Seq.slice (Seq.slice cipher from_pos to_pos) 0 l)
			    (Seq.slice cipher from_pos from_pos'))

(*+ counterblocks_suffix: 
	counterblocks starting from some domain x >= x_1
	is a suffix of counterblocks starting from x_1
 **)	
assume val counterblocks_suffix
       (#i:id{safeId i})
       (rgn:region)
       (x:domain i{ctr_0 i <^ x.ctr})
       (len:u32{len <> 0ul})
       (from_pos:nat{from_pos <= v len /\
 		   remaining_len_ok x len (u (v len - from_pos))})
       (plain:Plain.plain i (v len))
       (cipher:lbytes (v len))
   : Lemma (requires True)
 	   (ensures (
	    let x_1 = {iv=x.iv; ctr=otp_offset i} in
	    let cb_from = counterblocks i rgn x (v len) from_pos (v len) plain cipher in
	    let all_blocks = counterblocks i rgn x_1 (v len) 0 (v len) plain cipher in
	    let offset = v (x.ctr -^ x_1.ctr) in
	    offset <= Seq.length all_blocks /\ (
	    let all_blocks_suffix = Seq.slice all_blocks offset (Seq.length all_blocks) in 
	    Seq.equal cb_from all_blocks_suffix)))


val counterblocks_len: #i:id{safeId i} -> 
		       rgn:region -> 
		       x:domain i{ctr_0 i <^ x.ctr} ->
		       len:nat{len <> 0} ->
		       from_pos:nat{from_pos <= len /\ safelen i (len - from_pos) x.ctr} ->
		       plain:Plain.plain i len ->
		       cipher:lbytes len -> Lemma
  (ensures Seq.length (counterblocks i rgn x len from_pos len plain cipher) =
           num_blocks_for_len i (len - from_pos))
  (decreases (len - from_pos))
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec counterblocks_len #i rgn x len from_pos plain cipher =
  if from_pos = len
  then ()
  else let blockl = v (Cipher.(blocklen (cipherAlg_of_id i))) in
       let remaining = len - from_pos in
       let l0 = minNat remaining blockl in
       counterblocks_len #i rgn (PRF.incr i x) len (from_pos + l0) plain cipher

assume val counterblocks_contains_all_otp_blocks:   
  i:id{safeId i} ->
  r:rid -> 
  x:PRF.domain i ->
  len:u32 ->
  remaining_len:u32{remaining_len_ok x len remaining_len} ->
  plain:Crypto.Plain.plain i (v len) ->
  cipher:lbytes (v len) ->
  Lemma (requires True)
        (ensures
	    (let from_pos = v (len -^ remaining_len) in
	     let all_blocks = counterblocks i r x (v len) from_pos (v len) plain cipher in
	     prf_contains_all_otp_blocks x from_pos plain cipher all_blocks))

val counterblocks_suffix_contains_otp_blocks
    (i:id{safeId i})
    (r:region)
    (x:PRF.domain i)
    (#len:u32)
    (remaining_len:u32{remaining_len_ok x len remaining_len})
    (plain:Crypto.Plain.plain i (v len))
    (cipher:lbytes (v len))
    : Lemma 
	(requires True)
        (ensures
	    (let x_1 = {x with ctr=otp_offset i} in
	     let from_pos = v (len -^ remaining_len) in
	     let all_blocks = counterblocks i r x_1 (v len) 0 (v len) plain cipher in
	     let n_blocks = v x.ctr - v x_1.ctr in
	     n_blocks <= Seq.length all_blocks /\
	     (let cb_suffix = Seq.slice all_blocks n_blocks (Seq.length all_blocks) in
	      prf_contains_all_otp_blocks x from_pos plain cipher cb_suffix)))
let counterblocks_suffix_contains_otp_blocks
    (i:id{safeId i})
    (r:region)
    (x:PRF.domain i)
    (#len:u32)
    (remaining_len:u32{remaining_len_ok x len remaining_len})
    (plain:Crypto.Plain.plain i (v len))
    (cipher:lbytes (v len))
  = let x_1 = {x with ctr=otp_offset i} in
    let from_pos = v (len -^ remaining_len) in
    let all_blocks = counterblocks i r x_1 (v len) 0 (v len) plain cipher in
    let blocks_from_x = counterblocks i r x (v len) from_pos (v len) plain cipher in
    counterblocks_len r x_1 (v len) 0 plain cipher;
    counterblocks_contains_all_otp_blocks i r x len remaining_len plain cipher;
    counterblocks_suffix r x len from_pos plain cipher

assume val prf_contains_all_otp_blocks_tail
    (#i:id) 
    (#r:rid)
    (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
    (#len:nat)
    (from_pos:nat{len <> 0 /\ 
		from_pos < len /\ 
		safelen i (len - from_pos) PRF.(x.ctr) /\
		safelen i len (otp_offset i)
		})
    (plain:plain i len)
    (cipher:lbytes len)
    (prf_table:prf_table r i)
   : Lemma (requires (prf_contains_all_otp_blocks x from_pos plain cipher prf_table))
 	   (ensures  (let remaining_len = len - from_pos in
	              let l = minNat remaining_len (v (PRF.blocklen i)) in
		      prf_contains_all_otp_blocks (PRF.incr i x) (from_pos + l) plain cipher prf_table))


(*+ invert_prf_contains_all_otp_blocks:
	This restates prf_contains_all_otp_blocks inductively, 
	as a property of the first block and inductively on the tail
 **)
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
val invert_prf_contains_all_otp_blocks
    (#i:id) (#r:rid)
    (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
    (#len:nat)
    (from_pos:nat{len <> 0 /\ 
		from_pos < len /\ 
		safelen i (len - from_pos) PRF.(x.ctr) /\
		safelen i len (otp_offset i)
		})
    (plain:plain i len)
    (cipher:lbytes len)
    (blocks:prf_table r i{safeId i})
   : Lemma (requires (prf_contains_all_otp_blocks x from_pos plain cipher blocks))
 	   (ensures  (let remaining_len = len - from_pos in
	              let l = minNat remaining_len (v (PRF.blocklen i)) in
     		      let plain_hd = Plain.slice plain from_pos (from_pos + l) in
	              let cipher_hd = Seq.slice cipher from_pos (from_pos + l) in
		      PRF.contains_cipher_block l x cipher_hd blocks /\
     		      PRF.contains_plain_block x plain_hd blocks /\ 
		      prf_contains_all_otp_blocks (PRF.incr i x) (from_pos + l) plain cipher blocks))
let invert_prf_contains_all_otp_blocks #i #r x #len from_pos plain cipher blocks
   = if safeId i 
     then let otp_blocks = counterblocks i r x len from_pos len plain cipher in
	  SeqProperties.contains_intro otp_blocks 0 (SeqProperties.head otp_blocks);
	  prf_contains_all_otp_blocks_tail x from_pos plain cipher blocks
