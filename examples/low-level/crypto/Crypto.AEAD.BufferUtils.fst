module Crypto.AEAD.BufferUtils
open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Buffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type buffer = Buffer.buffer UInt8.t

abstract let prf_mac_modifies (prf_region:rid) (mac_region:rid) h0 h1 = 
  h0 == h1  \/
  (HS.modifies_transitively (as_set [prf_region]) h0 h1       /\ //only touched the prf's region (and its children)
   HS.modifies_ref mac_region TSet.empty h0 h1)                 //in the mac region, didn't touch any existing ref

let intro_prf_mac_modifies (prf_region:rid) (mac_region:rid) (h0:mem) (h1:mem)
  : Lemma (requires (h0 == h1  \/
		     (HS.modifies_transitively (as_set [prf_region]) h0 h1 /\ 
		      HS.modifies_ref mac_region TSet.empty h0 h1)))
          (ensures (prf_mac_modifies prf_region mac_region h0 h1))
  = ()

let dexor_modifies (c:bool) (prf_region:rid) (plain:buffer) (h0:mem) (h1:mem) =
   if c
   then Buffer.modifies_1 plain h0 h1
   else (HS.modifies (as_set [prf_region; frameOf plain]) h0 h1 /\
	 Buffer.modifies_buf_1 (frameOf plain) plain h0 h1)

let decrypt_modifies (prf_region:rid) (mac_region:rid)
		     (plain:buffer) (h0:mem) (h1:mem) : Type0 =  //TODO: strange, seem to need the Type0 annotation otherwise code below fails
  HS.modifies_transitively (as_set [prf_region; frameOf plain]) h0 h1 /\ 
  Buffer.modifies_buf_1 (Buffer.frameOf plain) plain h0 h1 /\
  HS.modifies_ref mac_region TSet.empty h0 h1

let accumulate_modifies_nothing h0 h1 = 
  let open HS in
  modifies_one h0.tip h0 h1
  /\ Buffer.modifies_buf_0 h0.tip h0 h1
  /\ h0.tip=h1.tip

val chain_modification: #a:Type -> 
			acc:FStar.Buffer.buffer a ->
			cond:bool -> 
			prf_region:rid -> 
			mac_region:rid -> 
			plain:buffer -> //plain
			h_init:mem -> 
			h0:mem -> //after push
			h1:mem -> //after prf_mac
			h2:mem -> //after accumulate
			h3:mem -> //after verify
			h4:mem -> //after dexor
     Lemma (requires 
	      Buffer.live h_init plain /\
	      prf_region `is_in` h_init.h /\
	      mac_region `is_in` h_init.h /\
	      is_eternal_region prf_region /\
	      is_eternal_region (frameOf plain) /\
	      prf_region `HH.includes` mac_region /\
	      prf_region <> mac_region /\
	      HH.disjoint (frameOf plain) prf_region /\
	      HS.fresh_frame h_init h0 /\                        //push
	      prf_mac_modifies prf_region mac_region h0 h1 /\    //prf_mac
	      accumulate_modifies_nothing h1 h2 /\               //accumulate
	      Buffer.frameOf acc = h2.tip /\
	      Buffer.modifies_1 acc h2 h3 /\                      //verify
	      (h3 == h4 \/ dexor_modifies cond prf_region plain h3 h4)) //maybe dexor
	    (ensures (HS.poppable h4 /\
		      decrypt_modifies prf_region mac_region plain h_init (HS.pop h4)))
#reset-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0 --z3rlimit 200"
let chain_modification #a acc cond prf_region mac_region plain h_init h0 h1 h2 h3 h4 =
    Buffer.lemma_reveal_modifies_1 acc h2 h3;
    FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 plain h3) h4
