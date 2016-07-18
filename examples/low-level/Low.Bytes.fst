module Low.Bytes

open FStar.Mul
open FStar.HyperStack
open FStar.HST
open FStar.Buffer

assume MaxUInt32: pow2 32 = 4294967296

(* Buffer types *)
let size = u:pos{u = 1 \/ u = 2 \/ u = 4 \/ u = 8 \/ u = 16}
type bytes_ (s:size) = buffer UInt8.t

let bytes = bytes_ 1
let u16s  = bytes_ 2
let u32s  = bytes_ 4
let u64s  = bytes_ 8

(* Conversions from bytes to other buffers *)
val bytes_to_u16s: b:bytes -> Tot u16s
let bytes_to_u16s b = let (b:buffer UInt8.t) = b in b

val bytes_to_u32s: bytes -> Tot u32s
let bytes_to_u32s b = let (b:buffer UInt8.t) = b in b

val bytes_to_u64s: bytes -> Tot u64s
let bytes_to_u64s b = let (b:buffer UInt8.t) = b in b

val u16s_to_bytes: u16s -> Tot bytes
let u16s_to_bytes b = let (b:buffer UInt8.t) = b in b

val u32s_to_bytes: u32s -> Tot bytes
let u32s_to_bytes b = let (b:buffer UInt8.t) = b in b

val u64s_to_bytes: u64s -> Tot bytes
let u64s_to_bytes b = let (b:buffer UInt8.t) = b in b

(* SizeOf assumptions *)
assume val size_of: t:Type -> Tot size

assume SizeOfU8:  size_of UInt8.t = 1
assume SizeOfU16: size_of UInt16.t = 2
assume SizeOfU32: size_of UInt32.t = 4
assume SizeOfU64: size_of UInt64.t = 8
assume SizeOfPtr: forall (a:Type). {:pattern (size_of (Buffer.buffer a))} size_of (Buffer.buffer a) = 8
assume SizeOfRef: forall (a:Type). {:pattern (size_of (HyperStack.stackref a))} size_of (HyperStack.stackref a) = 8

(* Type of functions that convert a value of type t into a sequence of bytes or the converse *)
type bytes_format (t:Type) = t -> Tot (s:Seq.seq UInt8.t{Seq.length s = size_of t})
type bytes_parse  (t:Type) = s:Seq.seq UInt8.t{Seq.length s = size_of t} -> Tot t

(* Examples of such functions *)
abstract let u16_to_b : bytes_format UInt16.t = fun x ->
  let s = Seq.create 2 0uy in
  let s = Seq.upd s 0 (Int.Cast.uint16_to_uint8 x) in
  let s = Seq.upd s 1 (Int.Cast.uint16_to_uint8 (UInt16.shift_right x 8ul)) in
  s
abstract let u32_to_b : bytes_format UInt32.t = fun x ->
  let s = Seq.create 4 0uy in
  let s = Seq.upd s 0 (Int.Cast.uint32_to_uint8 x) in
  let s = Seq.upd s 1 (Int.Cast.uint32_to_uint8 (UInt32.shift_right x 8ul)) in
  let s = Seq.upd s 2 (Int.Cast.uint32_to_uint8 (UInt32.shift_right x 16ul)) in
  let s = Seq.upd s 3 (Int.Cast.uint32_to_uint8 (UInt32.shift_right x 24ul)) in
  s
abstract let u64_to_b : bytes_format UInt64.t = fun x ->
  let s = Seq.create 8 0uy in
  let s = Seq.upd s 0 (Int.Cast.uint64_to_uint8 x) in
  let s = Seq.upd s 1 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 8ul)) in
  let s = Seq.upd s 2 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 16ul)) in
  let s = Seq.upd s 3 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 24ul)) in
  let s = Seq.upd s 4 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 32ul)) in
  let s = Seq.upd s 5 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 40ul)) in
  let s = Seq.upd s 6 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 48ul)) in
  let s = Seq.upd s 7 (Int.Cast.uint64_to_uint8 (UInt64.shift_right x 56ul)) in
  s
assume val ref_to_b : #a:Type -> bytes_format (HyperStack.stackref a)
assume val ptr_to_b : #a:Type -> bytes_format (Buffer.buffer a)

assume val b_to_u16: bytes_parse UInt16.t
assume val b_to_u32: bytes_parse UInt32.t
assume val b_to_u64: bytes_parse UInt64.t
assume val b_to_ref: #a:Type -> bytes_parse (HyperStack.stackref a)
assume val b_to_ptr: #a:Type -> len:Ghost.erased nat -> s:Seq.seq UInt8.t{Seq.length s = size_of (Buffer.buffer a)} -> Tot (buffer a)

(* Those functions have to be bijections *)
assume val lemma_u16_to_bytes_bij: x:UInt16.t -> Lemma
  (requires (True))
  (ensures  (b_to_u16 (u16_to_b x) = x))
  [SMTPat (u16_to_b x)]

assume val lemma_u32_to_bytes_bij: x:UInt32.t -> Lemma
  (requires (True))
  (ensures  (b_to_u32 (u32_to_b x) = x))
  [SMTPat (u32_to_b x)]

assume val lemma_u64_to_bytes_bij: x:UInt64.t -> Lemma
  (requires (True))
  (ensures  (b_to_u64 (u64_to_b x) = x))
  [SMTPat (u64_to_b x)]

(* Goes from a seq byte to a seq t and vice versa, to allow easy writing of functional 
   specifications *)
let rec to_seq_byte_aux (#t:Type) (f:bytes_format t) (s:Seq.seq t) (b:Seq.seq UInt8.t) : Tot (Seq.seq UInt8.t) (decreases (Seq.length s)) =
  if Seq.length s > 0 then 
    to_seq_byte_aux f (Seq.slice s 1 (Seq.length s)) (Seq.append b (f (Seq.index s 0)))
  else b
let to_seq_byte (#t:Type) (f:bytes_format t) (s:Seq.seq t): Tot (Seq.seq UInt8.t) =
  to_seq_byte_aux f s (Seq.create 0 0uy)

let rec of_seq_byte_aux (#t:Type) (f:bytes_parse t) (s:Seq.seq UInt8.t{exists (n:nat). Seq.length s = (size_of t) * n}) (b:Seq.seq t) : Tot (Seq.seq t) (decreases (Seq.length s)) =
  if Seq.length s > 0 then (
    assume (exists (n:nat). Seq.length (Seq.slice s (size_of t) (Seq.length s)) = size_of t * n);
    of_seq_byte_aux f (Seq.slice s (size_of t) (Seq.length s)) (Seq.append b (Seq.create 1 (f (Seq.slice s 0 (size_of t))))) 
    )
  else b
let of_seq_byte (#t:Type) (f:bytes_parse t) (s:Seq.seq UInt8.t{exists (n:nat). Seq.length s = (size_of t) * n}) : Tot (Seq.seq t) =
  of_seq_byte_aux f s (Seq.createEmpty)

assume val lemma_live_contains: #a:Type -> h:mem -> b:buffer a -> Lemma
  (requires (live h b))
  (ensures  (contains h b /\ max_length h b >= length b + idx b))
  [SMTPat   (live h b)]

let live #size h (b:bytes_ size) = live h b /\ (exists (n:nat). length b = n * size)

let length #size (b:bytes_ size) : GTot nat = length b / size


assume val lemma_live_b_to_u16: h:mem -> b:bytes -> Lemma
  (requires (live h b))
  (ensures  (live h (bytes_to_u16s b)))
  [SMTPatT (live h b); SMTPat (bytes_to_u16s b)]
assume val lemma_live_b_to_u32: h:mem -> b:bytes -> Lemma
  (requires (live h b))
  (ensures  (live h (bytes_to_u32s b)))
  [SMTPatT (live h b); SMTPat (bytes_to_u32s b)]
assume val lemma_live_b_to_u64: h:mem -> b:bytes -> Lemma
  (requires (live h b))
  (ensures  (live h (bytes_to_u64s b)))
  [SMTPatT (live h b); SMTPat (bytes_to_u64s b)]
assume val lemma_live_u16_to_b: h:mem -> b:u16s -> Lemma
  (requires (live h b))
  (ensures  (live h (u16s_to_bytes b)))
  [SMTPatT (live h b); SMTPat (u16s_to_bytes b)]
assume val lemma_live_u32_to_b: h:mem -> b:u32s -> Lemma
  (requires (live h b))
  (ensures  (live h (u32s_to_bytes b)))
  [SMTPatT (live h b); SMTPat (u32s_to_bytes b)]
assume val lemma_live_u64_to_b: h:mem -> b:u64s -> Lemma
  (requires (live h b))
  (ensures  (live h (u64s_to_bytes b)))
  [SMTPatT (live h b); SMTPat (u64s_to_bytes b)]

(* Concrete such functions *)
let to_seq8 h (b:bytes{live h b}) = as_seq h b
assume val to_seq16: h:mem -> b:u16s{live h b} -> GTot (s:Seq.seq UInt16.t{Seq.length s = length b})
assume val to_seq32: h:mem -> b:u32s{live h b} -> GTot (s:Seq.seq UInt32.t{Seq.length s = length b})
assume val to_seq64: h:mem -> b:u64s{live h b} -> GTot (s:Seq.seq UInt64.t{Seq.length s = length b})

(* Injectivity predicates *)
assume val lemma_to_seq8_bij: h:mem -> b:bytes{live h b} -> h':mem -> b':bytes{live h' b'} -> Lemma
  (requires (True))
  (ensures  (Seq.equal (to_seq8 h b) (to_seq8 h' b') <==> equal h b h' b'))
assume val lemma_to_seq16_bij: h:mem -> b:u16s{live h b} -> h':mem -> b':u16s{live h' b'} -> Lemma
  (requires (True))
  (ensures  (Seq.equal (to_seq16 h b) (to_seq16 h' b') <==> equal h b h' b'))
assume val lemma_to_seq32_bij: h:mem -> b:u32s{live h b} -> h':mem -> b':u32s{live h' b'} -> Lemma
  (requires (True))
  (ensures  (Seq.equal (to_seq32 h b) (to_seq32 h' b') <==> equal h b h' b'))
assume val lemma_to_seq64_bij: h:mem -> b:u64s{live h b} -> h':mem -> b':u64s{live h' b'} -> Lemma
  (requires (True))
  (ensures  (Seq.equal (to_seq64 h b) (to_seq64 h' b') <==> equal h b h' b'))

assume val create_8: len:UInt32.t -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq8 h1 b = Seq.create (UInt32.v len) 0uy))

assume val create_16: len:UInt32.t -> ST u16s
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq16 h1 b = Seq.create (UInt32.v len) 0us))

assume val create_32: len:UInt32.t -> ST u32s
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq32 h1 b = Seq.create (UInt32.v len) 0ul))

assume val create_64: len:UInt32.t -> ST u64s
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq64 h1 b = Seq.create (UInt32.v len) 0uL))

assume val read_8: b:bytes -> i:UInt32.t{UInt32.v i < length b} -> STL UInt8.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 = h0 /\ live h0 b /\ z = Seq.index (to_seq8 h0 b) (UInt32.v i)))

assume val read_16: b:u16s -> i:UInt32.t{UInt32.v i < length b} -> STL UInt16.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 = h0 /\ live h0 b /\ z = Seq.index (to_seq16 h0 b) (UInt32.v i)))

assume val read_32: b:u32s -> i:UInt32.t{UInt32.v i < length b} -> STL UInt32.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 = h0 /\ live h0 b /\ z = Seq.index (to_seq32 h0 b) (UInt32.v i)))

assume val read_64: b:u64s -> i:UInt32.t{UInt32.v i < length b} -> STL UInt64.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 = h0 /\ live h0 b /\ z = Seq.index (to_seq64 h0 b) (UInt32.v i)))

assume val write_8: b:bytes -> i:UInt32.t{UInt32.v i < length b} -> z:UInt8.t -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq8 h1 b = Seq.upd (to_seq8 h0 b) (UInt32.v i) z))

assume val write_16: b:u16s -> i:UInt32.t{UInt32.v i < length b} -> z:UInt16.t -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq16 h1 b = Seq.upd (to_seq16 h0 b) (UInt32.v i) z))

assume val write_32: b:u32s -> i:UInt32.t{UInt32.v i < length b} -> z:UInt32.t -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq32 h1 b = Seq.upd (to_seq32 h0 b) (UInt32.v i) z))

assume val write_64: b:u64s -> i:UInt32.t{UInt32.v i < length b} -> z:UInt64.t -> STL unit
  (requires (fun h -> live h b /\ UInt32.v i < length b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq64 h1 b = Seq.upd (to_seq64 h0 b) (UInt32.v i) z))

assume val memcpy_8: src:bytes -> srci:UInt32.t -> dest:bytes -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq8 h1 dest in let d0 = to_seq8 h0 dest in let s0 = to_seq8 h0 src in
        Seq.slice d1 0 (UInt32.v desti) = Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) = 
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) = 
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest)) ))

assume val memcpy_16: src:u16s -> srci:UInt32.t -> dest:u16s -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq16 h1 dest in let d0 = to_seq16 h0 dest in let s0 = to_seq16 h0 src in
        Seq.slice d1 0 (UInt32.v desti) = Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) = 
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) = 
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest) )))

assume val memcpy_32: src:u32s -> srci:UInt32.t -> dest:u32s -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq32 h1 dest in let d0 = to_seq32 h0 dest in let s0 = to_seq32 h0 src in
        Seq.slice d1 0 (UInt32.v desti) = Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) = 
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) = 
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest) )))

assume val memcpy_64: src:u64s -> srci:UInt32.t -> dest:u64s -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq64 h1 dest in let d0 = to_seq64 h0 dest in let s0 = to_seq64 h0 src in
        Seq.slice d1 0 (UInt32.v desti) = Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) = 
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) = 
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest) )))

assume val sub_8: b:bytes -> i:UInt32.t -> len:UInt32.t -> STL bytes
  (requires (fun h -> live h b /\ UInt32.v i + UInt32.v len <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = UInt32.v len
    /\ to_seq8 h1 b' = Seq.slice (to_seq8 h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len)
    ))

assume val sub_16: b:u16s -> i:UInt32.t -> len:UInt32.t -> STL u16s
  (requires (fun h -> live h b /\ UInt32.v i + UInt32.v len <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + 2*UInt32.v i /\ length b' = 2*UInt32.v len
    /\ to_seq16 h1 b' = Seq.slice (to_seq16 h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len)
    ))

assume val sub_32: b:u32s -> i:UInt32.t -> len:UInt32.t -> STL u32s
  (requires (fun h -> live h b /\ UInt32.v i + UInt32.v len <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + 4*UInt32.v i /\ length b' = 4*UInt32.v len
    /\ to_seq32 h1 b' = Seq.slice (to_seq32 h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len)
    ))

assume val sub_64: b:u64s -> i:UInt32.t -> len:UInt32.t -> STL u64s
  (requires (fun h -> live h b /\ UInt32.v i + UInt32.v len <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + 8*UInt32.v i /\ length b' = 8*UInt32.v len
    /\ to_seq64 h1 b' = Seq.slice (to_seq64 h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len)
    ))

assume val offset_8: b:bytes -> i:UInt32.t -> STL bytes
  (requires (fun h -> live h b /\ UInt32.v i <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = length b - UInt32.v i
    /\ to_seq8 h1 b' = Seq.slice (to_seq8 h0 b) (UInt32.v i) (length b) ))

assume val offset_16: b:u16s -> i:UInt32.t -> STL u16s
  (requires (fun h -> live h b /\ UInt32.v i <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + 2 * UInt32.v i /\ length b' = length b - 2 * UInt32.v i
    /\ to_seq16 h1 b' = Seq.slice (to_seq16 h0 b) (UInt32.v i) (length b) ))

assume val offset_32: b:u32s -> i:UInt32.t -> STL u32s
  (requires (fun h -> live h b /\ UInt32.v i <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + 4 * UInt32.v i /\ length b' = length b - 4 * UInt32.v i
    /\ to_seq32 h1 b' = Seq.slice (to_seq32 h0 b) (UInt32.v i) (length b) ))

assume val offset_64: b:u64s -> i:UInt32.t -> STL u64s
  (requires (fun h -> live h b /\ UInt32.v i <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 = h0
    /\ idx b' = idx b + 8 * UInt32.v i /\ length b' = length b - 8 * UInt32.v i
    /\ to_seq64 h1 b' = Seq.slice (to_seq64 h0 b) (UInt32.v i) (length b) ))
