(*--build-config
  options:--admit_fsi FStar.Set --verify_module Buffer32;
  other-files:FStar.Classical.fst FStar.PredicateExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axioms.fst intlib.fst sint.fst FStar.UInt8.fst sbuffer.fst;
  --*)

module FStar.SBytes

open FStar.Ghost
open FStar.Heap
open IntLib
open Sint
open FStar.UInt8
open FStar.UInt32
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

opaque type Equals (ha:heap) (a:buffer 32) (hb:heap) (b:sbytes) (l:nat) =
  l <= length a /\ 4 * l <= length b /\ Live ha a /\ Live hb b
  /\ (forall (i:nat). {:pattern (get ha a i) \/ get hb b (4*i+0) \/ get hb b (4*i+0) \/ get hb b (4*i+0) }
       i < l ==> v (get ha a i) = v (get hb b (4*i+0)) + pow2 8 * v (get hb b (4*i+1)) +
		         pow2 16 * v (get hb b (4*i+2)) + pow2 24 * v (get hb b (4*i+3)))

opaque type Equals64 (ha:heap) (a:buffer 64) (hb:heap) (b:sbytes) (l:nat) =
  l <= length a /\ 8 * l <= length b /\ Live ha a /\ Live hb b
  /\ (forall (i:nat). {:pattern (get ha a i) \/ get hb b (8*i+0) \/ get hb b (8*i+0) \/ get hb b (8*i+0) }
       i < l ==> v (get ha a i) = v (get hb b (8*i+0)) + pow2 8 * v (get hb b (8*i+1)) +
		         pow2 16 * v (get hb b (8*i+2)) + pow2 24 * v (get hb b (8*i+3)) +
               pow2 32 * v (get hb b (8*i+4)) + pow2 40 * v (get hb b (8*i+5)) +
               pow2 48 * v (get hb b (8*i+6)) + pow2 56 * v (get hb b (8*i+7)))

assume val uint32_of_sbytes: b:sbytes{length b >= 4} -> ST uint32
  (requires (fun h -> Live h b))
  (ensures (fun h0 r h1 -> Live h0 b /\ h0 == h1
			 /\ v r = v (get h0 b 0) + pow2 8 * v (get h0 b 1) +
			         pow2 16 * v (get h0 b 2) + pow2 24 * v (get h0 b 3)))

assume val sbytes_of_uint32: res:sbytes{length res >= 4} -> v:uint32 -> ST unit
  (requires (fun h -> Live h res))
  (ensures  (fun h0 r h1 -> Live h1 res /\ Modifies (only res) h0 h1))

assume val uint64_of_sbytes: b:sbytes{length b >= 8} -> ST uint64
  (requires (fun h -> Live h b))
  (ensures (fun h0 r h1 -> Live h0 b /\ h0 == h1
			 /\ v r = v (get h0 b 0) + pow2 8 * v (get h0 b 1)
                  + pow2 16 * v (get h0 b 2) + pow2 24 * v (get h0 b 3)
                  + pow2 32 * v (get h0 b 4) + pow2 40 * v (get h0 b 5)
                  + pow2 48 * v (get h0 b 6) + pow2 56 * v (get h0 b 7)))

assume val sbytes_of_uint64: res:sbytes{length res >= 8} -> v:uint64 -> ST unit
  (requires (fun h -> Live h res))
  (ensures  (fun h0 r h1 -> Live h1 res /\ Modifies (only res) h0 h1))

assume val be_sbytes_of_uint64: res:sbytes{length res >= 8} -> v:uint64 -> ST unit
  (requires (fun h -> Live h res))
  (ensures  (fun h0 r h1 -> Live h1 res /\ Modifies (only res) h0 h1))

assume val uint64s_of_sbytes: res:buffer 64 -> b:sbytes{Disjoint res b} -> l:nat{8*l<=length b /\ length res < l} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals64 h1 res h0 b l /\ Modifies (only res) h0 h1))

assume val be_uint64s_of_sbytes: res:buffer 64 -> b:sbytes{Disjoint res b} -> l:nat{8*l<=length b /\ length res < l} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals64 h1 res h0 b l /\ Modifies (only res) h0 h1))

assume val sbytes_of_uint64s: res:sbytes -> b:buffer 64{Disjoint res b} -> l:nat{l<=length b /\ 8*l <= length res} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals64 h0 b h1 res l /\ Modifies (only res) h0 h1))

assume val be_sbytes_of_uint64s: res:sbytes -> b:buffer 64{Disjoint res b} -> l:nat{l<=length b /\ 8*l <= length res} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals64 h0 b h1 res l /\ Modifies (only res) h0 h1))

assume val uint128_of_sbytes: b:sbytes{length b >= 16} -> ST uint128
  (requires (fun h -> Live h b))
  (ensures (fun h0 r h1 -> Live h0 b /\ h0 == h1
			 /\ v r = v (get h0 b 0) + pow2 8 * v (get h0 b 1)
                  + pow2 16 * v (get h0 b 2) + pow2 24 * v (get h0 b 3)
                  + pow2 32 * v (get h0 b 4) + pow2 40 * v (get h0 b 5)
                  + pow2 48 * v (get h0 b 6) + pow2 56 * v (get h0 b 7)
                  + pow2 64 * v (get h0 b 8) + pow2 72 * v (get h0 b 9)
                  + pow2 80 * v (get h0 b 10) + pow2 88 * v (get h0 b 11)
                  + pow2 96 * v (get h0 b 12) + pow2 104 * v (get h0 b 13)
                  + pow2 112 * v (get h0 b 14) + pow2 120 * v (get h0 b 15)))

assume val sbytes_of_uint128: res:sbytes{length res >= 16} -> v:uint128 -> ST unit
  (requires (fun h -> Live h res))
  (ensures  (fun h0 r h1 -> Live h1 res /\ Modifies (only res) h0 h1))

assume val be_sbytes_of_uint128: res:sbytes{length res >= 16} -> v:uint128 -> ST unit
  (requires (fun h -> Live h res))
  (ensures  (fun h0 r h1 -> Live h1 res /\ Modifies (only res) h0 h1))

assume val uint32s_of_sbytes: res:buffer 32 -> b:sbytes{Disjoint res b} -> l:nat{4*l<=length b /\ length res < l} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals h1 res h0 b l /\ Modifies (only res) h0 h1))

assume val be_uint32s_of_sbytes: res:buffer 32 -> b:sbytes{Disjoint res b} -> l:nat{4*l<=length b /\ length res < l} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals h1 res h0 b l /\ Modifies (only res) h0 h1))

assume val sbytes_of_uint32s: res:sbytes -> b:buffer 32{Disjoint res b} -> l:nat{l<=length b /\ 4*l <= length res} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals h0 b h1 res l /\ Modifies (only res) h0 h1))

assume val be_sbytes_of_uint32s: res:sbytes -> b:buffer 32{Disjoint res b} -> l:nat{l<=length b /\ 4*l <= length res} -> ST unit
  (requires (fun h -> Live h res /\ Live h b))
  (ensures (fun h0 _ h1 -> Equals h0 b h1 res l /\ Modifies (only res) h0 h1))

(* TODO : do something to make sure that if output is a or b it still works *)
assume val xor_bytes: output:sbytes -> a:sbytes -> b:sbytes{Disjoint a b} -> l:nat{l <= length b /\ l <= length a /\ l <= length output} -> ST unit
  (requires (fun h -> Live h output /\ Live h a /\ Live h b))
  (ensures (fun h0 _ h1 -> Live h0 a /\ Live h0 b /\ Live h1 output /\ Modifies (only output) h0 h1
    /\ (forall (i:nat). {:pattern (get h1 output i)} i < l ==>
      v (get h1 output i) = v (FStar.UInt8.logxor (get h0 a i) (get h0 b i))) ))

assume val print: sbytes -> Tot unit
assume val print_bytes: sbytes -> Tot unit
