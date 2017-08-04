module F1

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.BaseTypes
open FStar.UInt32
open FStar.Buffer

let buffer_equal (m:mem) (dst:buffer uint8) (src:buffer uint8) (size:nat) = true

val  memcpy: (dst:buffer uint8)->(src:buffer uint8)->(size:uint32)->ST unit
      (requires (fun h -> live h dst /\ live h src /\ (v size) >0 /\ length dst >= (v size) /\ length src >= (v size)))
      (ensures (fun h0 r h1 -> live h1 dst /\ live h1 dst /\ buffer_equal h1 dst src (v size)))
let memcpy dst src size = 
    let c = index src 0ul in
    upd dst 0ul c
    
