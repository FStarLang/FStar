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

(*** COUNTERS AND LENGTHS ***)
(* The ctr value associated with the first otp block *)
let otp_offset (i:id) = ctr_0 i +^ 1ul

let aadlen = x:UInt32.t{x <=^ aadmax}

let maxplain (i:id) = pow2 14 // for instance

let num_blocks_for_len (i:id) (l:nat) : Tot nat =
  let bl = v (Cipher.( blocklen (cipherAlg_of_id i))) in
  (l + bl - 1) / bl

(** safelen: The length of the plaintext is not too large **)
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

(** remaining_len_ok: 
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

noeq type aead_state (i:id) (rw:rw) =
  | AEADState:
      #log_region: rgn -> // this is the *writer* region; the reader allocates nothing
      // the log should exist only when prf i
      (* TODO: this should follow the pattern used everywhere else:
	 log: if safeId i then HS.ref (Seq.seq (entry i)) else unit
      *)
      log: HS.ref (Seq.seq (aead_entry i)) {HS.frameOf log == log_region} ->
      // Was PRF(prf.rgn) == region. Do readers use its own PRF state?
      prf: PRF.state i {prf.rgn == log_region /\
		       (Flag.prf i ==> ~(log === PRF.itable i prf)) } (* including its key *) ->
      ak: CMA.akey prf.mac_rgn i (* static, optional authentication key *) ->
      aead_state i rw

(*** MAIN STATEFUL INVARIANT ***)

(** Some utilities for stating the invariant **)
noextract let is_aead_entry_nonce (#i:id) (n:Cipher.iv (alg i)) (e:aead_entry i) =
  e.nonce = n

noextract let find_aead_entry (#i:id) (n:Cipher.iv (alg i)) (entries:Seq.seq (aead_entry i))
  : option (aead_entry i)
  = SeqProperties.find_l (is_aead_entry_nonce n) entries

let fresh_nonce (#i:id) (#rw:rw) (n:Cipher.iv (alg i)) (aead_st:aead_state i rw) (h:mem) = 
  let entries = HS.sel h aead_st.log in
  None? (find_aead_entry n entries)

let num_blocks_for_entry (#i:id) (e:aead_entry i) : Tot nat =
  let AEADEntry nonce ad l plain cipher_tagged = e in
  num_blocks_for_len i l

let encode_ad_cipher (i:id) (ad:adata) (l:plainLen{safelen i l (PRF.ctr_0 i +^ 1ul)}) (cipher:lbytes l) =
  encode_both i (FStar.UInt32.uint_to_t (Seq.length ad)) ad (FStar.UInt32.uint_to_t l) cipher

(** counterblocks:
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
    let block = PRF.Entry x (PRF.OTP l_32 plain_hd cipher_hd) in 
    let blocks = counterblocks i mac_rgn (PRF.incr i x) l (from_pos + l0) to_pos plain cipher in
    SeqProperties.cons block blocks

(** mac_is_set prf_table iv: 
        the mac entry in the prf_table, at location (iv, ctr_0 i)
	is set to the suitable encoded ad + cipher, tag      **)
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_is_set (#rgn:region) (#i:id)
	       (prf_table:prf_table rgn i{safeId i}) //the entire prf table
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
       let mac_log = CMA.ilog (CMA.State?.log mac_range) in
       m_contains mac_log h /\ (
       match m_sel h mac_log with
       | None           -> False
       | Some (msg,tag') ->
	 safelen i l (PRF.ctr_0 i +^ 1ul) /\
	 msg = encode_ad_cipher i ad l cipher /\
 	 tag = tag'))

(** refines_one_entry:
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
   let dom_1 = {iv=iv; ctr=PRF.ctr_0 i +^ 1ul} in
   safelen i l dom_1.ctr /\ //it's not too long
   //1. the mac entry for this nonce in the prf table contains a mac'd ad+cipher
   mac_is_set prf_table iv ad l cipher tag h /\
   //2. all the expected otp_blocks are in the table, in some order
   //NB: this does not forbid the prf_table from containing other OTP blocks with the same IV;
   //    not clear whether we need that
   (let otp_blocks = counterblocks i rgn dom_1 l 0 l plain cipher in
    (forall (prf_entry:PRF.entry rgn i).
      otp_blocks `contains` prf_entry ==>
      PRF.find prf_table prf_entry.x == Some (prf_entry.range)))

(** none_above x prf_table:
	no entry in the prf_table at ({iv=x.iv; ctr=i}) for any i >= x.ctr **)
let none_above (#r:region) (#i:id) (x:PRF.domain i) (prf_table:prf_table r i) =
    forall (y:PRF.domain i{y `PRF.above` x}). PRF.find prf_table y == None

(** none_above_if_authId x prf_state h:
        A stateful variant of none_above, using the full prf_table in h **)
let none_above_if_authId (#i:id) (x:PRF.domain i) (st:PRF.state i) (h:mem) =
  CMA.authId (i, x.iv) ==>
    (let prf_table = HS.sel h (itable i st) in
     none_above x prf_table)

(** all_above x prf_blocks
	every entry in the prf_blocks is above x  ({iv=x.iv; ctr=i}) for any i >= x.ctr

	This is generally used for some sequence of prf entries,
	not the full prf table
**)
let all_above (#rgn:region) (#i:id) (x:PRF.domain i) (s:prf_table rgn i) =
  (forall (e:PRF.entry rgn i).{:pattern (s `SeqProperties.contains` e)}
     s `SeqProperties.contains` e ==> e.x `PRF.above` x)

(** unused_aead_iv_for_prf prf_table iv:
	the iv is either fresh, i.e., doesn't appear anywhere in the prf_table
	Or, it occurs there with an unused mac (e.g., decrypt allocated one early)
 **)
let unused_aead_iv_for_prf (#mac_rgn:region) (#i:id)
			   (prf_table:prf_table mac_rgn i) //the entire prf table
  			   (iv:Cipher.iv (alg i))
			   (h:mem{safeId i}) : GTot Type0
  = let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
    none_above (PRF.incr i dom_0) prf_table /\ //There are no OTP entries for this IV at all
    (match PRF.find_mac prf_table dom_0 with
     | None           -> True //and no MAC entry either
     | Some mac_range -> CMA.mac_is_unset (i, iv) mac_rgn mac_range h) //Or, a mac exists, but it's not yet used

(** refines prf_table aead_entries h:
	THE MAIN CLAUSE OF THE STATEFUL INVARIANT:
	In state h, prf_table refines aead_entries
 **)
let refines (#rgn:region) (#i:id)
            (prf_table: prf_table rgn i)
	    (aead_entries:Seq.seq (aead_entry i))
	    (h:mem{safeId i}) : GTot Type0 =
  let open FStar.SeqProperties in
  (* 1. Each aead entry is refined by the PRF table *)
  (forall (aead_entry:aead_entry i).
    aead_entries `contains` aead_entry ==>
    refines_one_entry prf_table aead_entry h) /\
  (* 2. Every iv that does not appear in the aead table is unused in the PRF table *)
  (forall (iv:Cipher.iv (alg i)).
    match find_aead_entry iv aead_entries with
    | Some _ -> True //already covered by refines_one_entry
    | None   -> unused_aead_iv_for_prf prf_table iv h)

(** aead_liveness:
	The aead_state and its regions etc. are live **)
let aead_liveness (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) : Type0 =
  HS.(h.h `Map.contains` st.prf.mac_rgn) /\      //contains the mac region
  (safeId i ==> h `HS.contains` st.log) /\       //contains the aead log
  (prf i ==> h `HS.contains` (itable i st.prf)) //contains the prf table


(*** inv st h:
       The final stateful invariant,
       refines and aead_state_live ***)
let inv (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) : Type0 =
  aead_liveness st h /\
  (safeId i ==>
     (let prf_table = HS.sel h (itable i st.prf) in
      let aead_entries = HS.sel h st.log in
      refines prf_table aead_entries h))


(*** SEPARATION AND LIVENESS
     REQUIREMENTS OF THE INTERFACE ***)

module Plain = Crypto.Plain
(** enc_dec_separation:
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

(** enc_dec_liveness:
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

let u (n:FStar.UInt.uint_t 32) = uint_to_t n

(** Framing lemmas for clauses of the main invariant **)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_refines_one_entry (#i:id{safeId i}) (#mac_rgn:region) 
			    (h:mem) (h':mem) 
			    (blocks:prf_table mac_rgn i)
			    (e:aead_entry i) 
   : Lemma (requires (let open HS in
		      refines_one_entry blocks e h /\			    
		      HH.modifies_rref mac_rgn TSet.empty h.h h'.h /\
		      live_region h' mac_rgn))
	   (ensures  refines_one_entry blocks e h')
   = ()

let frame_unused_aead_iv_for_prf (#mac_rgn:region) (#i:id) (h0:mem{safeId i}) (h1:mem)
				 (prf_table:prf_table mac_rgn i)
				 (iv:Cipher.iv (alg i))
  : Lemma (requires (let open HS in
		     unused_aead_iv_for_prf prf_table iv h0        /\
                     HH.modifies_rref mac_rgn TSet.empty h0.h h1.h /\
		     live_region h1 mac_rgn))
	  (ensures  unused_aead_iv_for_prf prf_table iv h1)
  = ()

let frame_refines (i:id{safeId i}) (mac_rgn:region) 
		  (blocks:prf_table mac_rgn i)
		  (entries:aead_entries i)
		  (h:mem) (h':mem)
   : Lemma (requires (let open HS in 
		      refines blocks entries h                     /\
   		      HH.modifies_rref mac_rgn TSet.empty h.h h'.h /\
		      HS.live_region h' mac_rgn))
	   (ensures  refines blocks entries h')
   = let open FStar.Classical in
     forall_intro (move_requires (frame_refines_one_entry h h' blocks));
     forall_intro (move_requires (frame_unused_aead_iv_for_prf h h' blocks))

let frame_inv_push (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) (h1:mem)
   : Lemma (requires (inv st h /\ 
		      HS.fresh_frame h h1))
	   (ensures (inv st h1))
   = if safeId i
     then frame_refines i st.prf.mac_rgn (HS.sel h (PRF.itable i st.prf)) (HS.sel h st.log) h h1

let weaken_all_above (#rgn:region) (#i:id) (s:Seq.seq (PRF.entry rgn i)) 
		    (x:PRF.domain i) (y:PRF.domain i{y `above` x})
    : Lemma (all_above y s ==> all_above x s)
    = ()

(** counterblocks_emp:
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

(** Lemmas about searching for entries in prf_blocks **)
let find_append (#i:id) (#r:rid) (d:domain i) (s1:prf_table r i) (s2:prf_table r i)
   : Lemma (requires (None? (find s1 d)))
           (ensures (find (Seq.append s1 s2) d == find s2 d))
   = SeqProperties.find_append_none s1 s2 (is_entry_domain d)

#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 2 --max_fuel 2"
let find_singleton (#rgn:region) (#i:id) (e:PRF.entry rgn i) (x:PRF.domain i) 
    : Lemma (if is_entry_domain x e then PRF.find (Seq.create 1 e) x == Some e.range
	     else PRF.find (Seq.create 1 e) x == None)
    = ()	     
