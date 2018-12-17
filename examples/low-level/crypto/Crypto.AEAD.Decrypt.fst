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
module Crypto.AEAD.Decrypt
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.HyperStack.ST
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant

module HH       = FStar.HyperHeap
module HS       = FStar.HyperStack
module ST       = FStar.HyperStack.ST
module MAC      = Crypto.Symmetric.MAC
module CMA      = Crypto.Symmetric.UF1CMA
module Plain    = Crypto.Plain
module Cipher   = Crypto.Symmetric.Cipher
module PRF      = Crypto.Symmetric.PRF
module Dexor       = Crypto.AEAD.EnxorDexor
module Encoding    = Crypto.AEAD.Encoding   
module EncodingWrapper = Crypto.AEAD.Wrappers.Encoding
module CMAWrapper = Crypto.AEAD.Wrappers.CMA
module PRF_MAC    = Crypto.AEAD.Wrappers.PRF

////////////////////////////////////////////////////////////////////////////////
//decrypt
////////////////////////////////////////////////////////////////////////////////
let decrypt_modifies (#i:id) (#len:u32) (st:aead_state i Reader) (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   Crypto.AEAD.BufferUtils.decrypt_modifies st.log_region st.prf.mac_rgn (as_buffer pb) h0 h1

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let post_pop (#i:id) (n:Cipher.iv (alg i)) (st:aead_state i Reader) 
	     (#aadlen:aadlen) (aad:lbuffer (v aadlen))
	     (#plainlen:txtlen_32) 
	     (plain:plainBuffer i (v plainlen))
	     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	     (verified:bool)
	     (h:mem{HS.poppable h})
    : Lemma (requires (enc_dec_separation st aad plain cipher_tagged /\
		       enc_dec_liveness st aad plain cipher_tagged h /\
		       inv st h /\
		       (verified ==> Dexor.decrypt_ok n st aad plain cipher_tagged h)))
	    (ensures  (let h = HS.pop h in
		       enc_dec_separation st aad plain cipher_tagged /\
		       enc_dec_liveness st aad plain cipher_tagged h /\
		       inv st h /\
		       (verified ==> Dexor.decrypt_ok n st aad plain cipher_tagged h)))
    = if safeMac i
      then frame_refines i st.prf.mac_rgn (HS.sel h (PRF.itable i st.prf)) (HS.sel h (st_ilog st)) h (HS.pop h)

val chain_mods (#i:id) (#n:Cipher.iv (alg i)) 
	       (st:aead_state i Reader) 
	       (#aadlen:aadlen) (aad:lbuffer (v aadlen))
	       (#plainlen:txtlen_32) (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
       	       (acc:CMA.accBuffer (i, n))
	       (h_init:mem)
	       (h0:mem) //after push
	       (h1:mem) //after prf_mac
	       (h2:mem) //after accumulate
	       (h3:mem) //after verify
	       (h4:mem) //after dexor
    : Lemma (requires (let x_1 = {iv=n; ctr=otp_offset i} in 
		       enc_dec_separation st aad plain cipher_tagged /\
		       enc_dec_liveness st aad plain cipher_tagged h_init /\
		       HS.fresh_frame h_init h0 /\
		       BufferUtils.prf_mac_modifies st.log_region st.prf.mac_rgn h0 h1 /\    //prf_mac
		       EncodingWrapper.accumulate_modifies_nothing h1 h2 /\
	       	       Buffer.frameOf (MAC.as_buffer (CMA.abuf acc)) = HS.(h2.tip) /\
       		       CMAWrapper.verify_modifies acc h2 h3 /\
		       (h3 == h4 \/ Dexor.dexor_modifies st.prf x_1 plain h3 h4)))
	    (ensures  (HS.poppable h4 /\
	    	       decrypt_modifies st plain h_init (HS.pop h4)))
let chain_mods #i #n st #aadlen aad #plainlen plain cipher_tagged acc h_init h0 h1 h2 h3 h4
     = let abuf = MAC.as_buffer (CMA.abuf acc) in 
       let cond = not (prf i) || safeId i in 
       BufferUtils.chain_modification abuf cond st.log_region st.prf.mac_rgn (Plain.as_buffer plain) h_init h0 h1 h2 h3 h4

val decrypt:
  i:id -> 
  st:aead_state i Reader ->
  n:Cipher.iv (alg i) ->
  aadlen:aadlen ->
  aad:lbuffer (v aadlen) ->
  plainlen:nz_ok_len_32 i ->
  plain:plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
  ST bool
  (requires (fun h ->
    enc_dec_separation st aad plain cipher_tagged /\
    enc_dec_liveness st aad plain cipher_tagged h /\
    inv st h))
  (ensures (fun h0 verified h1 ->
    enc_dec_liveness st aad plain cipher_tagged h1 /\
    inv st h1 /\
    decrypt_modifies st plain h0 h1 /\
    (verified ==> Dexor.decrypt_ok n st aad plain cipher_tagged h1)))
#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_inv_push st h_init h0;
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  let x_0 = PRF.({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = PRF_MAC.prf_mac_dec st aad plain cipher_tagged st.ak x_0 in   // used for keying the one-time MAC
  let h1 = get() in
  // First recompute and check the MAC
  let acc = EncodingWrapper.accumulate #(i,iv) st ak aad plain cipher_tagged in
  let h2 = get () in
  let popt = CMAWrapper.verify st aad plain cipher_tagged ak acc h1 in
  let h3 = get () in
  let verified : bool = 
    match popt with 
    | None -> false
    | Some p -> 
      Dexor.dexor st iv aad plain cipher_tagged p;
      true in 
  let h4 = get () in
  chain_mods st aad plain cipher_tagged acc h_init h0 h1 h2 h3 h4;
  post_pop iv st aad plain cipher_tagged verified h4;
  pop_frame();
  verified
