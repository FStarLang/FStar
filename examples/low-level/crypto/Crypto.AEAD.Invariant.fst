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

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let ctr x = PRF(x.ctr)

noeq type aead_entry (i:id) =
  | AEADEntry:
      nonce:Cipher.iv (alg i) ->
      ad:adata ->
      l:plainLen ->
      p:plain i l ->
      c:cipher i (Seq.length (as_bytes p)) ->
      aead_entry i

let prf_table (r:rgn) (i:id) = Seq.seq (PRF.entry r i)
let aead_entries i = Seq.seq (aead_entry i)

noextract let is_aead_entry_nonce (#i:id) (n:Cipher.iv (alg i)) (e:aead_entry i) =
  e.nonce = n

noextract let find_aead_entry (#i:id) (n:Cipher.iv (alg i)) (entries:Seq.seq (aead_entry i))
  : option (aead_entry i)
  = SeqProperties.find_l (is_aead_entry_nonce n) entries

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

let maxplain (i:id) = pow2 14 // for instance

(* safelen: The length of the plaintext is not too large *)
let safelen (i:id)
	    (remaining_len:nat)  //the length of plaintext left to be encrypted;
	    (next_block_index:UInt32.t) //the counter for encrypting the next block of plaintext
  =
  let open FStar.Mul in
  PRF.ctr_0 i <^ next_block_index &&                  //next_block_index is strictly greater than the mac domain position
  next_block_index <=^ PRF.maxCtr i &&               //and less then the max counter
  (let block_length = v (Cipher( blocklen (cipherAlg_of_id i))) in
   let len_all_blocks_so_far = v (next_block_index -^ PRF.ctr_0 i -^ 1ul) * block_length in
   let max_len_for_remaining_blocks = v (PRF.maxCtr i -^ next_block_index) * block_length in
   remaining_len = 0 ||                               //no more text left to encrypt, or
   (remaining_len + len_all_blocks_so_far <= maxplain i &&
    remaining_len <= max_len_for_remaining_blocks))

// Computes PRF table contents for countermode encryption of 'plain' to 'cipher' starting from 'x'.
val counterblocks:
  i:id {safeId i} ->
  rgn:region ->  //the rgn is really superfluous,
		//since it is only potentially relevant in the case of the mac,
		//but that's always Seq.createEmpty here
                //16-10-13 but still needed in the result type, right?
  x:PRF.domain i{PRF.ctr_0 i <^ ctr x} ->
  l:nat ->
  from_pos:nat ->
  to_pos:nat{from_pos <= to_pos /\ to_pos <= l /\ safelen i (to_pos - from_pos) (ctr x)} ->
  plain:Crypto.Plain.plain i l ->
  cipher:lbytes l ->
  Tot (prf_table rgn i) // each entry e {PRF(e.x.id = x.iv /\ e.x.ctr >= ctr x)}
  (decreases (to_pos - from_pos))
let rec counterblocks i rgn x l from_pos to_pos plain cipher =
  let blockl = v (Cipher(blocklen (cipherAlg_of_id i))) in
  let remaining = to_pos - from_pos in
  if remaining = 0 then
    Seq.createEmpty
  else
    let l0 = minNat remaining blockl in
    let l_32 = UInt32.uint_to_t l0 in
    let plain_hd = Crypto.Plain.slice plain from_pos (from_pos + l0) in
    let cipher_hd = Seq.slice cipher from_pos (from_pos + l0) in
    let block = PRF.Entry x (PRF.OTP l_32 plain_hd cipher_hd) in
    let blocks = counterblocks i rgn (PRF.incr i x) l (from_pos + l0) to_pos plain cipher in
    SeqProperties.cons block blocks

let num_blocks_for_len (i:id) (l:nat) : Tot nat =
  let bl = v (Cipher( blocklen (cipherAlg_of_id i))) in
  (l + bl - 1) / bl

let num_blocks_for_entry (#i:id) (e:aead_entry i) : Tot nat =
  let AEADEntry nonce ad l plain cipher_tagged = e in
  num_blocks_for_len i l

let encode_ad_cipher (i:id) (ad:adata) (l:plainLen{safelen i l (PRF.ctr_0 i +^ 1ul)}) (cipher:lbytes l) =
  encode_both i (FStar.UInt32.uint_to_t (Seq.length ad)) ad (FStar.UInt32.uint_to_t l) cipher

#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_is_set (#rgn:region) (#i:id{safeId i})
	       (prf_table:prf_table rgn i) //the entire prf table
	       (iv:Cipher.iv (alg i))
	       (ad:adata)
	       (l:plainLen)
	       (cipher:lbytes l)
	       (tag:MAC.tag)
	       (h:mem) : GTot Type0
  = let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
    //2. the mac entry for this nonce in the prf table contains a mac'd ad+cipher
    (match PRF.find_mac prf_table dom_0 with
     | None -> False
     | Some mac_range ->
       let mac_log = CMA.ilog (CMA.State.log mac_range) in
       m_contains mac_log h /\ (
       match m_sel h mac_log with
       | None           -> False
       | Some (msg,tag') ->
	 safelen i l (PRF.ctr_0 i +^ 1ul) /\
	 msg = encode_ad_cipher i ad l cipher /\
 	 tag = tag'))

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

let none_above (#r:region) (#i:id) (x:PRF.domain i) (prf_table:prf_table r i) (h:mem) =
    CMA.authId (i, x.iv) ==> (forall (y:PRF.domain i{y `PRF.above` x}). PRF.find prf_table y == None)

let all_above (#rgn:region) (#i:id) (s:prf_table rgn i) (x:PRF.domain i) =
  (forall (e:PRF.entry rgn i).{:pattern (s `SeqProperties.contains` e)}
     s `SeqProperties.contains` e ==> e.x `PRF.above` x)

let mac_is_unset (#rgn:region) (#i:id)
	         (prf_table:prf_table rgn i) //the entire prf table
  	         (iv:Cipher.iv (alg i))
		 (h:mem{safeId i}) : GTot Type0
  = let dom_0 = {iv=iv; ctr=PRF.ctr_0 i} in
    none_above (PRF.incr i dom_0) prf_table h /\ //There are no OTP entries for this IV at all
    (match PRF.find_mac prf_table dom_0 with
     | None -> True //and no MAC entry either
     | Some mac_range ->
       let mac_log = CMA.ilog (CMA.State.log mac_range) in
       m_contains mac_log h /\ (
       match m_sel h mac_log with
       | None           ->  True //or, MAC entry exists, but it is not yet used
       | Some (msg,tag') -> False))

(** THE MAIN CLAUSE OF THE STATEFUL INVARIANT:
    States consistency of the PRF table contents vs the AEAD entries
 **)
let refines (#rgn:region) (#i:id)
            (prf_table: prf_table rgn i)
	    (aead_entries:Seq.seq (aead_entry i))
	    (h:mem{safeId i}) : GTot Type0 =
  let open FStar.SeqProperties in
  (forall (aead_entry:aead_entry i).
    aead_entries `contains` aead_entry ==>
    refines_one_entry prf_table aead_entry h) /\
  (forall (iv:Cipher.iv (alg i)).
    match find_aead_entry iv aead_entries with
    | Some _ -> True //already covered by refines_one_entry
    | None -> mac_is_unset prf_table iv h)

let aead_liveness (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) : Type0 =
  HS (h.h `Map.contains` st.prf.mac_rgn) /\      //contains the mac region
  (safeId i ==> h `HS.contains` st.log) /\       //contains the aead log
  (prf i ==> h `HS.contains` (itable i st.prf)) //contains the prf table

(*** MAIN STATEFUL INVARIANT ***)
let inv (#i:id) (#rw:rw) (st:aead_state i rw) (h:mem) : Type0 =
  aead_liveness st h /\
  (safeId i ==>
     (let prf_table = HS.sel h (itable i st.prf) in
      let aead_entries = HS.sel h st.log in
      refines prf_table aead_entries h))


(* TODO: Move this out of here to be closer to AEAD.encrypt, where it is mainly used *)
let modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i)
				      (x:PRF.domain i) (b:lbuffer l)
				      (h0:HS.mem) (h1:HS.mem) =
  Buffer.live h1 b /\
  (if prf i then
    let r = PRF.itable i t in
    let rb = Buffer.frameOf b in
    let rgns = Set.union (Set.singleton #HH.rid t.rgn) (Set.singleton #HH.rid rb) in
    let contents0 = HS.sel h0 r in
    let contents1 = HS.sel h1 r in
    HS.modifies rgns h0 h1 /\
    HS.modifies_ref t.rgn (TSet.singleton (FStar.Heap.Ref (HS.as_ref r))) h0 h1 /\
    Buffer.modifies_buf_1 rb b h0 h1 /\
    Seq.length contents0 <= Seq.length contents1 /\
    Seq.equal (Seq.slice contents1 0 (Seq.length contents0)) contents0 /\
    all_above (Seq.slice contents1 (Seq.length contents0) (Seq.length contents1)) x
  else
    Buffer.modifies_1 b h0 h1)

(* The ctr value associated with the first otp block *)
let otp_offset (i:id) = ctr_0 i +^ 1ul

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
   else completed_len = FStar.Mul (n_blocks * v (PRF.blocklen i)))

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
