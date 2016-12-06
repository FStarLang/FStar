module Crypto.AEAD.Encrypt.Lemmas

// Implements agile, conditionally secure Authenticated Encryption
// with Associated Data (AEAD) for TLS 1.2 and 1.3, given secure, 
// agile PRF cipher and UF-1CMA MAC. 

// For the security proof, we maintain a stateful invariant that
// precisely relates the contents of the AEAD log to the states of the
// PRF and the MACs.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Invariant

module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain
module Invariant = Crypto.AEAD.Invariant
module HS = FStar.HyperStack



#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val extend_refines_aux: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) ->
		       (aadlen: UInt32.t {aadlen <=^ aadmax}) ->
		       (aad: lbuffer (v aadlen)) ->
                       (len:nat{len<>0}) -> (plain:plainBuffer i len) -> (cipher:lbuffer (len + v MAC.taglen)) ->
		       (h0:mem) ->
                       (h1:mem{Buffer.live h1 aad /\ Plain.live h1 plain /\ Buffer.live h1 cipher}) ->
    Lemma (requires ( safeId i ==> (
		      let mac_rgn = st.prf.mac_rgn in
      		      let entries_0 = HS.sel h0 st.log in 
		      let blocks_0 = HS.sel h0 (PRF.itable i st.prf) in
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
		      Seq.length table_1 > Seq.length blocks_0 /\ (
		      let blocks_1 = Seq.slice table_1 (Seq.length blocks_0) (Seq.length table_1) in

     		      let p = Plain.sel_plain h1 (u len) plain in
		      let c_tagged = Buffer.as_seq h1 cipher in
	              let c, tag = SeqProperties.split c_tagged len in
		      let ad = Buffer.as_seq h1 aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      pre_refines_one_entry i st nonce len plain cipher h0 h1 /\
		      inv h0 st /\
		      refines_one_entry #_ #i h1 entry blocks_1 /\
      		      HS.modifies_ref mac_rgn TSet.empty h0 h1 /\
		      HS.live_region h1 mac_rgn))))
		      
          (ensures ( safeId i ==> (
		      let mac_rgn = st.prf.mac_rgn in
      		      let entries_0 = HS.sel h0 st.log in 
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     		      let p = Plain.sel_plain h1 (u len) plain in
		      let c_tagged = Buffer.as_seq h1 cipher in
	              let c, tag = SeqProperties.split c_tagged len in
		      let ad = Buffer.as_seq h1 aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      refines h1 i mac_rgn (SeqProperties.snoc entries_0 entry) table_1)))
let extend_refines_aux i st nonce aadlen aad len plain cipher h0 h1 = 
  if safeId i then
     let mac_rgn = st.prf.mac_rgn in
     let entries_0 = HS.sel h0 st.log in 
     let blocks_0 = HS.sel h0 (PRF.itable i st.prf) in
     let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     let blocks_1 = Seq.slice table_1 (Seq.length blocks_0) (Seq.length table_1) in
     let p = Plain.sel_plain h1 (u len) plain in
     let c_tagged = Buffer.as_seq h1 cipher in
     let c, tag = SeqProperties.split c_tagged len in
     let ad = Buffer.as_seq h1 aad in
     let entry = Entry nonce ad len p c_tagged in
     extend_refines h0 i mac_rgn entries_0 blocks_0 entry blocks_1 h1
