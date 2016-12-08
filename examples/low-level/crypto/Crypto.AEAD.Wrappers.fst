module Crypto.AEAD.Wrappers

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

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module CMA = Crypto.Symmetric.UF1CMA
module MAC = Crypto.Symmetric.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain

////////////////////////////////////////////////////////////////////////////////
//Wrappers encapsulate the calls to various routines used in encrypt/decrypt

//16-11-04 We should indicate that the real accumulator may also be updated;
//16-11-04 (we don't care since it won't be re-used, as we lose acc_inv)
//Move to UF1CMA, together with some lemmas.

////////////////////////////////////////////////////////////////////////////////
//AEAD.Encoding.accumulate wrapper
////////////////////////////////////////////////////////////////////////////////
let accumulate_liveness (#i: MAC.id) (st: CMA.state i) 
			(#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
			(#txtlen:txtlen_32) (cipher:lbuffer (v txtlen)) (h:mem) = 
  MAC.norm h CMA.(st.r) /\
  Buffer.live h aad /\ 
  Buffer.live h cipher

// modifies only fresh buffers on the current stack
let accumulate_modifies_nothing h0 h1 = 
  let open HS in
  modifies_one h0.tip h0 h1
  /\ Buffer.modifies_buf_0 h0.tip h0 h1
  /\ h0.tip=h1.tip

let fresh_sref (#a:Type0) h0 h1 (r:HS.reference a) = 
  ~ (h0 `HS.contains` r) /\
    HS.frameOf r == HS.(h1.tip) /\
    h1 `HS.contains` r


(* let accumulate_encoded (#i:CMA.id) *)
(*  		       (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen)) *)
(* 		       (#plainlen:txtlen_32) (cipher:lbuffer (v plainlen)) *)
(* 		       (a:CMA.accBuffer i) (h:mem{mac_log}) = *)
(*     Buffer.live h aad /\			  *)
(*     Buffer.live h cipher /\			      *)
(*     h `HS.contains` (CMA.alog a) /\ *)
(*     HS.sel h (CMA.alog a) == *)
(*     encode_both (fst i) aadlen (Buffer.as_seq h aad) plainlen (Buffer.as_seq h cipher) *)

let accumulate_ensures (#i: MAC.id) (st: CMA.state i) 
		       (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		       (#txtlen:txtlen_32) (cipher:lbuffer (v txtlen))
		       (h0:mem) (a:CMA.accBuffer i) (h1:mem) =
  let open HS in		       
  let open CMA in 		       
  accumulate_liveness st aad cipher h1 /\
  fresh_sref h0 h1 (Buffer.content (MAC.as_buffer a.a)) /\
  CMA.acc_inv st a h1 /\
  (mac_log ==> 
    fresh_sref h0 h1 (alog a) /\
    HS.sel h1 (alog a) == encode_both (fst i) aadlen (Buffer.as_seq h1 aad) txtlen (Buffer.as_seq h1 cipher))
    
let accumulate (#i: MAC.id) (st: CMA.state i) (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
	       (#txtlen:txtlen_32) (cipher:lbuffer (v txtlen))
   : StackInline (CMA.accBuffer i)
      (requires (fun h0 -> 
	  accumulate_liveness st aad cipher h0))
      (ensures (fun h0 a h1 ->  
      	  accumulate_liveness st aad cipher h0 /\
          accumulate_modifies_nothing h0 h1 /\
	  accumulate_ensures st aad cipher h0 a h1))
  = let h0 = get () in
    let acc = accumulate #i st aadlen aad txtlen cipher in
    let h1 = get () in
    assert (Buffer.disjoint_2 (MAC.as_buffer (CMA.(acc.a))) (CMA.(st.s)) cipher);
    assume (mac_log ==> fresh_sref h0 h1 (CMA.alog acc)); //NS: this goes away when Encoding.accumulate is restored
    assume (fresh_sref h0 h1 (Buffer.content (MAC.as_buffer CMA.(acc.a))));
    FStar.Buffer.lemma_reveal_modifies_0 h0 h1;
    acc
////////////////////////////////////////////////////////////////////////////////
//end AEAD.Encoding.accumulate wrapper
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
//UF1CMA.mac wrapper
////////////////////////////////////////////////////////////////////////////////
#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_ensures (i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB)
		(h0:mem) (h1:mem) = 
    let open FStar.Buffer in
    let open Crypto.Symmetric.Bytes in
    let open Crypto.Symmetric.Poly1305 in
    let open Crypto.Symmetric.UF1CMA in
    Buffer.live h0 st.s /\ 
    MAC.live h0 st.r /\ 
    Buffer.live h1 tag /\
    CMA.acc_inv st acc h0 /\ (
    if mac_log then
      HS.modifies (Set.as_set [st.region; Buffer.frameOf tag]) h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let a = MAC.sel_elem h1 (abuf acc) in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let t = MAC.mac log r s in
      sel_word h1 tag === t /\
      m_sel h1 (ilog st.log) == Some(log,t))
    else Buffer.modifies_1 tag h0 h1)

let mac_wrapper (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB)
  : ST unit
  (requires (fun h0 ->
    let open Crypto.Symmetric.UF1CMA in
    Buffer.live h0 tag /\ 
    Buffer.live h0 st.s /\
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) st.s tag /\
    Buffer.disjoint (MAC.as_buffer st.r) tag /\
    Buffer.disjoint st.s tag /\ 
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 -> mac_ensures i st acc tag h0 h1))
  = let open Crypto.Symmetric.UF1CMA in
    let h0 = get () in
    CMA.mac #i st acc tag;
    let h1 = get () in 
    if mac_log then begin
      (* Need to update UF1CMA to prove this (problem with the mods clause not working fully) *)
      assume (HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1) //NS: this goes away when UF1CMA is done
    end
////////////////////////////////////////////////////////////////////////////////
//end UF1CMA.mac wrapper
////////////////////////////////////////////////////////////////////////////////



//16-11-04 disjoint st.r st.s comes from the UF1CMA state
//16-11-04 BTW Buffer.disjoint_2 should be strengthened to imply 3 disjoints
//Move to HS?

////////////////////////////////////////////////////////////////////////////////
//UF1CMA.verify
////////////////////////////////////////////////////////////////////////////////
let verify_liveness (#i:CMA.id) (st:CMA.state i) (tag:lbuffer 16) (h:mem) =
    Buffer.live h (CMA.(st.s)) /\
    Buffer.live h (CMA.(MAC.as_buffer st.r)) /\
    Buffer.live h tag
    
let verify_requires (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) (h0:mem) = 
    let open Crypto.Symmetric.UF1CMA in
    verify_liveness st tag h0 /\
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) st.s tag /\
    Buffer.disjoint_2 (MAC.as_buffer st.r) st.s tag /\
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (authId i ==> Some? (m_sel h0 (ilog st.log)))
			     
let verify_ok (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		     (h:mem{verify_liveness st tag h}) (b:bool)  = 
    let open Crypto.Symmetric.UF1CMA in
    if mac_log then 
      let log = FStar.HyperStack.sel h (alog acc) in
      let r = MAC.sel_elem h st.r in
      let s = Buffer.as_seq h st.s in
      let m = MAC.mac log r s in
      let verified = Seq.eq m (MAC.sel_word h tag) in
      if authId i then
      	match m_sel h (ilog st.log) with
      	| Some(l',m') ->
      	  let correct = m = m' && Seq.eq log l' in
      	  b == (verified && correct)
      	| None -> b==false
      else b==verified
    else True
		  
let verify_ensures (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		   (h0:mem) (b:bool) (h1:mem) = 
    Buffer.modifies_0 h0 h1 /\
    verify_liveness st tag h1 /\
    verify_ok st acc tag h1 b

val verify_wrapper: 
  #i:CMA.id -> 
  st:CMA.state i -> 
  acc:CMA.accBuffer i -> 
  tag:lbuffer 16 -> Stack bool
  (requires (fun h0 -> verify_requires st acc tag h0))
  (ensures (fun h0 b h1 -> verify_ensures st acc tag h0 b h1))
#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let verify_wrapper #i st acc tag = 
  let h0 = get () in 
  let b = CMA.verify #i st acc tag in
  let h1 = get() in
  Buffer.lemma_reveal_modifies_0 h0 h1;
  assert (mac_log ==> m_sel h0 (CMA.(ilog st.log)) == m_sel h1 (CMA.(ilog st.log)));
  b
////////////////////////////////////////////////////////////////////////////////
//end UF1CMA.verify
////////////////////////////////////////////////////////////////////////////////
