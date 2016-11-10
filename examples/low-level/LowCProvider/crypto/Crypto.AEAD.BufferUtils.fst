module Crypto.AEAD.BufferUtils
open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Buffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type buffer = Buffer.buffer UInt8.t

let prf_mac_modifies (c:bool) (r:rid) h0 h1 = 
  if c then h0 == h1 else modifies_transitively (as_set [r]) h0 h1

let dexor_modifies (c:bool) (r:rid) (b:buffer) (h0:mem) (h1:mem) =
   if c
   then Buffer.modifies_1 b h0 h1
   else (HS.modifies_transitively (as_set [r; frameOf b]) h0 h1 /\
	 Buffer.modifies_buf_1 (frameOf b) b h0 h1)

let decrypt_modifies (c:bool) (r:rid) (b:buffer) (h0:mem) (h1:mem) = 
  if c
  then Buffer.modifies_1 b h0 h1
  else  HS.modifies_transitively (as_set [r; frameOf b]) h0 h1 /\
        Buffer.modifies_buf_1 (frameOf b) b h0 h1

val chain_modification: cond:bool -> log_region:rid -> b:buffer -> 
			(h_init:mem) -> (h0:mem) ->(h1:mem)-> (h2:mem) -> (h3:mem) -> (h4:mem) ->
     Lemma (requires
	      Buffer.live h_init b /\
	      log_region `is_in` h_init.h /\
	      is_eternal_region log_region /\
	      is_eternal_region (frameOf b) /\
	      HH.disjoint (frameOf b) log_region /\
	      HS.fresh_frame h_init h0 /\
	      prf_mac_modifies cond log_region h0 h1 /\
	      Buffer.modifies_0 h1 h2 /\
	      Buffer.modifies_0 h2 h3 /\
	      (h3 == h4 \/ dexor_modifies cond log_region b h3 h4))
	    (ensures (HS.poppable h4 /\
		      decrypt_modifies cond log_region b h_init (HS.pop h4)))
#reset-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0 --z3timeout 100"
let chain_modification cond log_region b h_init h0 h1 h2 h3 h4 =
    Buffer.lemma_reveal_modifies_0 h1 h2;
    Buffer.lemma_reveal_modifies_0 h2 h3;
    FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 b h3) h4;
    if cond then begin
      assert (HS.modifies (as_set [h0.tip]) h0 h3);
      Buffer.lemma_intro_modifies_1 b h_init (HS.pop h4)
    end
    else ()
