module SBytes

open FStar.Ghost
open FStar.Heap
open Axioms
open IntLib
open SInt
open SInt.UInt8
open SInt.UInt32
open SBuffer

(* Contains coercion functions between integers and bytes that can be optimized in low-level code *)

type sbytes = buffer 8
type uint32 = usint 32
type uint64 = usint 64
type uint128 = usint 128

(**)
let create = create #8
let index = index #8
let upd = upd #8
let sub = sub #8
let blit = blit #8
let split = split #8
let copy = copy #8
let offset = offset #8
(**)

let equals (ha:heap) (a:buffer 32) (hb:heap) (b:sbytes) (l:nat) : GTot Type0 =
  l <= length a /\ 4 * l <= length b /\ live ha a /\ live hb b
  /\ (forall (i:nat). {:pattern (get ha a i) \/ get hb b (4*i+0) \/ get hb b (4*i+0) \/ get hb b (4*i+0) }
       i < l ==> v (get ha a i) = v (get hb b (4*i+0)) + pow2 8 * v (get hb b (4*i+1)) +
		         pow2 16 * v (get hb b (4*i+2)) + pow2 24 * v (get hb b (4*i+3)))

assume val uint32_of_sbytes: b:sbytes{length b >= 4} -> ST uint32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> live h0 b /\ h0 == h1
			 /\ v r = v (get h0 b 0) + pow2 8 * v (get h0 b 1) +
			         pow2 16 * v (get h0 b 2) + pow2 24 * v (get h0 b 3)))

assume val uint64_of_sbytes: b:sbytes{length b >= 8} -> ST uint64
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> live h0 b /\ h0 == h1
			 /\ v r = v (get h0 b 0) + pow2 8 * v (get h0 b 1)
                  + pow2 16 * v (get h0 b 2) + pow2 24 * v (get h0 b 3)
                  + pow2 32 * v (get h0 b 4) + pow2 40 * v (get h0 b 5)
                  + pow2 48 * v (get h0 b 6) + pow2 56 * v (get h0 b 7)))

assume val sbytes_of_uint64: res:sbytes{length res >= 8} -> v:uint64 -> ST unit
  (requires (fun h -> live h res))
  (ensures  (fun h0 r h1 -> live h1 res /\ modifies_buf (only res) h0 h1))

assume val be_sbytes_of_uint64: res:sbytes{length res >= 8} -> v:uint64 -> ST unit
  (requires (fun h -> live h res))
  (ensures  (fun h0 r h1 -> live h1 res /\ modifies_buf (only res) h0 h1))

assume val uint128_of_sbytes: b:sbytes{length b >= 16} -> ST uint128
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> live h0 b /\ h0 == h1
			 /\ v r = v (get h0 b 0) + pow2 8 * v (get h0 b 1)
                  + pow2 16 * v (get h0 b 2) + pow2 24 * v (get h0 b 3)
                  + pow2 32 * v (get h0 b 4) + pow2 40 * v (get h0 b 5)
                  + pow2 48 * v (get h0 b 6) + pow2 56 * v (get h0 b 7)
                  + pow2 64 * v (get h0 b 8) + pow2 72 * v (get h0 b 9)
                  + pow2 80 * v (get h0 b 10) + pow2 88 * v (get h0 b 11)
                  + pow2 96 * v (get h0 b 12) + pow2 104 * v (get h0 b 13)
                  + pow2 112 * v (get h0 b 14) + pow2 120 * v (get h0 b 15)))

assume val sbytes_of_uint128: res:sbytes{length res >= 16} -> v:uint128 -> ST unit
  (requires (fun h -> live h res))
  (ensures  (fun h0 r h1 -> live h1 res /\ modifies_buf (only res) h0 h1))

assume val be_sbytes_of_uint128: res:sbytes{length res >= 16} -> v:uint128 -> ST unit
  (requires (fun h -> live h res))
  (ensures  (fun h0 r h1 -> live h1 res /\ modifies_buf (only res) h0 h1))

assume val uint32s_of_sbytes: res:buffer 32 -> b:sbytes{disjoint res b} -> l:nat{4*l<=length b /\ l <= length res} -> ST unit
  (requires (fun h -> live h res /\ live h b))
  (ensures (fun h0 _ h1 -> equals h1 res h0 b l /\ modifies_buf (only res) h0 h1))

assume val be_uint32s_of_sbytes: res:buffer 32 -> b:sbytes{disjoint res b} -> l:nat{4*l<=length b /\ l <= length res} -> ST unit
  (requires (fun h -> live h res /\ live h b))
  (ensures (fun h0 _ h1 -> equals h1 res h0 b l /\ modifies_buf (only res) h0 h1))

assume val sbytes_of_uint32s: res:sbytes -> b:buffer 32{disjoint res b} -> l:nat{l<=length b /\ 4*l <= length res} -> ST unit
  (requires (fun h -> live h res /\ live h b))
  (ensures (fun h0 _ h1 -> equals h0 b h1 res l /\ modifies_buf (only res) h0 h1))

assume val be_sbytes_of_uint32s: res:sbytes -> b:buffer 32{disjoint res b} -> l:nat{l<=length b /\ 4*l <= length res} -> ST unit
  (requires (fun h -> live h res /\ live h b))
  (ensures (fun h0 _ h1 -> equals h0 b h1 res l /\ modifies_buf (only res) h0 h1))

(* TODO : do something to make sure that if output is a or b it still works *)
assume val xor_bytes: output:sbytes -> a:sbytes -> b:sbytes{disjoint a b} -> l:nat{l <= length b /\ l <= length a /\ l <= length output} -> ST unit
  (requires (fun h -> live h output /\ live h a /\ live h b))
  (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 output /\ modifies_buf (only output) h0 h1
    /\ (forall (i:nat). {:pattern (get h1 output i)} i < l ==>
      v (get h1 output i) = v (SInt.UInt8.logxor (get h0 a i) (get h0 b i))) ))

assume val print: sbytes -> Tot unit
assume val print_bytes: sbytes -> Tot unit
