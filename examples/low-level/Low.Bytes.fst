module Low.Bytes

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

assume MaxUInt32: pow2 32 = 4294967296

(* Buffer types *)
assume type hasSize (t:Type) : Type0

let serializable = t:Type{hasSize t}

assume HasSizeUInt8 : hasSize UInt8.t
assume HasSizeUInt16: hasSize UInt16.t
assume HasSizeUInt32: hasSize UInt32.t
assume HasSizeUInt64: hasSize UInt64.t
assume HasSizeBuffer: forall (a:serializable). {:pattern (buffer a)} hasSize (buffer a)
assume HasSizeRef: forall (a:serializable). {:pattern (HyperStack.stackref a)} hasSize (HyperStack.stackref a)

(* SizeOf assumptions *)
assume val sizeof: t:Type -> Tot pos

assume SizeOfU8:  sizeof UInt8.t = 1
assume SizeOfU16: sizeof UInt16.t = 2
assume SizeOfU32: sizeof UInt32.t = 4
assume SizeOfU64: sizeof UInt64.t = 8
assume SizeOfBuffer: forall (a:serializable). {:pattern (sizeof (buffer a))} sizeof (buffer a) = 8
assume SizeOfRef: forall (a:serializable). {:pattern (sizeof (HyperStack.stackref a))} sizeof (HyperStack.stackref a) = 8

(* Serialized any serializable into a sequence of (sizeof t) bytes *)
assume val serialize: #t:serializable -> x:t -> Tot (s:Seq.seq UInt8.t{Seq.length s = sizeof t})
(* Inflates a sequence of (sizeof t) bytes into an object of serializable t *)
assume val inflate: t:serializable -> s:Seq.seq UInt8.t{Seq.length s = sizeof t} -> Tot t

assume SerializeBijective: forall (t:serializable) (x:t). {:pattern (serialize #t x)}
  (inflate t (serialize #t x) == x)

let lemma_serialize_injective (#t:serializable) (x:t) (y:t) : Lemma
  (requires (serialize x == serialize y))
  (ensures  (x == y))
  [SMTPat (x == y)]
  = ()

let bytes = buffer UInt8.t

type buffer (t:serializable) = b:buffer UInt8.t{length b % (sizeof t) = 0}

assume HasSizeBuffer2: forall (a:serializable). {:pattern (buffer a)} hasSize (buffer a)
assume SizeOfBuffer2: forall (a:serializable). {:pattern (sizeof (buffer a))} sizeof (buffer a) = 8

let u16s  = buffer UInt16.t
let u32s  = buffer UInt32.t
let u64s  = buffer UInt64.t

(** Conversions from bytes to other buffers **)
(* Generic one *)
val ptr_cast: #t:serializable -> t':serializable -> b:buffer t{length b % sizeof t' = 0} -> Tot (b':buffer t')
let ptr_cast #t t' b =
  let b':bytes = b in b'

(* Specialized ones *)
let bytes_to_u16s b = ptr_cast #UInt8.t UInt16.t b
let bytes_to_u32s b = ptr_cast #UInt8.t UInt32.t b
let bytes_to_u64s b = ptr_cast #UInt8.t UInt64.t b
let u16s_to_bytes b = ptr_cast #UInt16.t UInt8.t b
let u16s_to_u32s b = ptr_cast #UInt16.t UInt32.t b
let u16s_to_u64s b = ptr_cast #UInt16.t UInt64.t b
let u32s_to_bytes b = ptr_cast #UInt32.t UInt8.t b
let u32s_to_u16s b = ptr_cast #UInt32.t UInt16.t b
let u32s_to_u64s b = ptr_cast #UInt32.t UInt64.t b
let u64s_to_bytes b = ptr_cast #UInt64.t UInt8.t b
let u64s_to_u16s b = ptr_cast #UInt64.t UInt16.t b
let u64s_to_u32s b = ptr_cast #UInt64.t UInt32.t b

(* Specialized serialize functions *)
let u16_to_b = serialize #UInt16.t
let u32_to_b = serialize #UInt32.t
let u64_to_b = serialize #UInt64.t
let ref_to_b (#a:serializable) = serialize #(HyperStack.stackref a)
let buf_to_b (#a:serializable) = serialize #(buffer a)

let b_to_u16 = inflate UInt16.t
let b_to_u32 = inflate UInt32.t
let b_to_u64 = inflate UInt64.t
let b_to_ref (#a:serializable) = inflate (HyperStack.stackref a)
let b_to_ptr (#a:serializable) = inflate (buffer a)

(* Goes from a seq byte to a seq t and vice versa *)
val to_seq_bytes: #t:serializable -> s:Seq.seq t -> 
  Tot (s':Seq.seq UInt8.t{Seq.length s' = sizeof t * Seq.length s}) 
  (decreases (Seq.length s))
let rec to_seq_bytes #t s =
  if Seq.length s = 0 then Seq.empty #UInt8.t
  else Seq.append (serialize #t (Seq.index s 0)) (to_seq_bytes (Seq.slice s 1 (Seq.length s)))

assume val lemma_aux_0: x:nat -> y:pos -> Lemma
  (requires (x > 0 /\ x % y = 0))
  (ensures  (x - y >= 0 /\ (x - y) % y = 0))

val of_seq_bytes: t:serializable -> s:Seq.seq UInt8.t{Seq.length s % sizeof t = 0} ->
  Tot (s':Seq.seq t{Seq.length s = sizeof t * Seq.length s'})
  (decreases (Seq.length s))
let rec of_seq_bytes t s =
  if Seq.length s = 0 then Seq.empty #t
  else begin
    lemma_aux_0 (Seq.length s) (sizeof t);
    Seq.append (Seq.create 1 (inflate t (Seq.slice s 0 (sizeof t)))) (of_seq_bytes t (Seq.slice s (sizeof t) (Seq.length s)))
  end

assume val lemma_live_contains: #a:serializable -> h:mem -> b:buffer a -> Lemma
  (requires (live h b))
  (ensures  (contains h b /\ max_length h b >= length b + idx b))
  [SMTPat   (live h b); SMTPat (hasSize a)]

let live #a h (b:buffer a) = live h b /\ length b % sizeof a = 0
let length #a (b:buffer a) : GTot nat = length b / sizeof a

val lemma_live_b_to_u16s: h:mem -> b:bytes{Buffer.length b % sizeof UInt16.t = 0} -> Lemma
  (requires (Buffer.live h b))
  (ensures  (live h (bytes_to_u16s b)))
  [SMTPat (Buffer.live h b); SMTPat (bytes_to_u16s b)]
let lemma_live_b_to_u16s h b = ()
val lemma_live_b_to_u32s: h:mem -> b:bytes{Buffer.length b % sizeof UInt32.t = 0} -> Lemma
  (requires (Buffer.live h b))
  (ensures  (live h (bytes_to_u32s b)))
  [SMTPat (Buffer.live h b); SMTPat (bytes_to_u32s b)]
let lemma_live_b_to_u32s h b = ()
val lemma_live_b_to_u64s: h:mem -> b:bytes{Buffer.length b % sizeof UInt64.t = 0} -> Lemma
  (requires (Buffer.live h b))
  (ensures  (live h (bytes_to_u64s b)))
  [SMTPat (Buffer.live h b); SMTPat (bytes_to_u64s b)]
let lemma_live_b_to_u64s h b = ()
val lemma_live_u16s_to_bytes: h:mem -> b:u16s -> Lemma
  (requires (live h b))
  (ensures  (live h (u16s_to_bytes b)))
  [SMTPat (Buffer.live h b); SMTPat (u16s_to_bytes b)]
let lemma_live_u16s_to_bytes h b = ()
val lemma_live_u16s_to_u32s: h:mem -> b:u16s{Buffer.length b % sizeof UInt32.t = 0} -> Lemma
  (requires (live h b))
  (ensures  (live h (u16s_to_u32s b)))
  [SMTPat (Buffer.live h b); SMTPat (u16s_to_u32s b)]
let lemma_live_u16s_to_u32s h b = ()
val lemma_live_u16s_to_u64s: h:mem -> b:u16s{Buffer.length b % sizeof UInt64.t = 0} -> Lemma
  (requires (live h b))
  (ensures  (live h (u16s_to_u64s b)))
  [SMTPat (Buffer.live h b); SMTPat (u16s_to_u64s b)]
let lemma_live_u16s_to_u64s h b = ()
val lemma_live_u32s_to_bytes: h:mem -> b:u32s -> Lemma
  (requires (live h b))
  (ensures  (live h (u32s_to_bytes b)))
  [SMTPat (Buffer.live h b); SMTPat (u32s_to_bytes b)]
let lemma_live_u32s_to_bytes h b = ()
val lemma_live_u32s_to_u16s: h:mem -> b:u32s -> Lemma
  (requires (live h b))
  (ensures  (live h (u32s_to_u16s b)))
  [SMTPat (Buffer.live h b); SMTPat (u32s_to_u16s b)]
let lemma_live_u32s_to_u16s h b = ()
val lemma_live_u32s_to_u64s: h:mem -> b:u32s{Buffer.length b % sizeof UInt64.t = 0} -> Lemma
  (requires (live h b))
  (ensures  (live h (u32s_to_u64s b)))
  [SMTPat (Buffer.live h b); SMTPat (u32s_to_u64s b)]
let lemma_live_u32s_to_u64s h b = ()
val lemma_live_u64s_to_bytes: h:mem -> b:u64s -> Lemma
  (requires (live h b))
  (ensures  (live h (u64s_to_bytes b)))
  [SMTPat (Buffer.live h b); SMTPat (u64s_to_bytes b)]
let lemma_live_u64s_to_bytes h b = ()
val lemma_live_u64s_to_u16s: h:mem -> b:u64s -> Lemma
  (requires (live h b))
  (ensures  (live h (u64s_to_u16s b)))
  [SMTPat (Buffer.live h b); SMTPat (u64s_to_u16s b)]
let lemma_live_u64s_to_u16s h b = ()
val lemma_live_u64s_to_u32s: h:mem -> b:u64s -> Lemma
  (requires (live h b))
  (ensures  (live h (u64s_to_u32s b)))
  [SMTPat (Buffer.live h b); SMTPat (u64s_to_u32s b)]
let lemma_live_u64s_to_u32s h b = ()

(* Mapping from mem * buffer 'a -> Seq 'a to sequences *)
val to_seq: #t:serializable -> h:mem -> b:buffer t{live h b} -> GTot (s:Seq.seq t{Seq.length s = length b})
let to_seq #t h b = of_seq_bytes t (as_seq h b)

(* Bijectivity predicates *)
assume val lemma_eq_refl: #t:serializable -> 
  h:mem -> b:buffer t{live h b} -> h':mem -> b':buffer t{live h' b'} -> Lemma
  (requires (to_seq h b == to_seq h' b'))
  (ensures  (equal h b h' b'))
  [SMTPat (equal h b h' b'); SMTPat (live h b)]

assume val lemma_eq_elim: #t:serializable -> 
  h:mem -> b:buffer t{live h b} -> h':mem -> b':buffer t{live h' b'} -> Lemma
  (requires (equal h b h' b'))
  (ensures  (to_seq h b == to_seq h' b'))
  [SMTPat (equal h b h' b'); SMTPat (live h b)]

(* Concrete operators on buffers *)
assume val create_8: len:UInt32.t -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live #UInt8.t h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq h1 b == Seq.create (UInt32.v len) 0uy))

assume val create_16: len:UInt32.t -> ST u16s
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq h1 b == Seq.create (UInt32.v len) 0us))

assume val create_32: len:UInt32.t -> ST u32s
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq h1 b == Seq.create (UInt32.v len) 0ul))

assume val create_64: len:UInt32.t -> ST u64s
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b)
    /\ frameOf b = h0.tip /\ to_seq h1 b == Seq.create (UInt32.v len) 0uL))

assume val read_8: b:bytes -> i:UInt32.t{UInt32.v i < length #UInt8.t b} -> STL UInt8.t
  (requires (fun h -> live #UInt8.t h b))
  (ensures  (fun h0 z h1 -> h1 == h0 /\ live #UInt8.t h0 b /\ z = Seq.index (to_seq h0 b) (UInt32.v i)))

assume val read_16: b:u16s -> i:UInt32.t{UInt32.v i < length b} -> STL UInt16.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 == h0 /\ live h0 b /\ z = Seq.index (to_seq h0 b) (UInt32.v i)))

assume val read_32: b:u32s -> i:UInt32.t{UInt32.v i < length b} -> STL UInt32.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 == h0 /\ live h0 b /\ z = Seq.index (to_seq h0 b) (UInt32.v i)))

assume val read_64: b:u64s -> i:UInt32.t{UInt32.v i < length b} -> STL UInt64.t
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 == h0 /\ live h0 b /\ z = Seq.index (to_seq h0 b) (UInt32.v i)))

assume val write_8: b:bytes -> i:UInt32.t{UInt32.v i < length #UInt8.t b} -> z:UInt8.t -> STL unit
  (requires (fun h -> live #UInt8.t h b))
  (ensures  (fun h0 _ h1 -> live #UInt8.t h0 b /\ live #UInt8.t h1 b /\ modifies_1 b h0 h1
    /\ to_seq h1 b == Seq.upd (to_seq h0 b) (UInt32.v i) z))

assume val write_16: b:u16s -> i:UInt32.t{UInt32.v i < length b} -> z:UInt16.t -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq h1 b == Seq.upd (to_seq h0 b) (UInt32.v i) z))

assume val write_32: b:u32s -> i:UInt32.t{UInt32.v i < length b} -> z:UInt32.t -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq h1 b == Seq.upd (to_seq h0 b) (UInt32.v i) z))

assume val write_64: b:u64s -> i:UInt32.t{UInt32.v i < length b} -> z:UInt64.t -> STL unit
  (requires (fun h -> live h b /\ UInt32.v i < length b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq h1 b == Seq.upd (to_seq h0 b) (UInt32.v i) z))

assume val memcpy_8: src:bytes -> srci:UInt32.t -> dest:bytes -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live #UInt8.t h src /\ live #UInt8.t h dest /\ disjoint src dest 
    /\ length #UInt8.t src >= UInt32.v srci + UInt32.v len /\ length #UInt8.t dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live #UInt8.t h0 src /\ live #UInt8.t h0 dest /\ live #UInt8.t h1 dest /\ modifies_1 dest h0 h1
    /\ length #UInt8.t src >= UInt32.v srci + UInt32.v len 
    /\ length #UInt8.t dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq #UInt8.t h1 dest in let d0 = to_seq #UInt8.t h0 dest in let s0 = to_seq #UInt8.t h0 src in
        Seq.slice d1 0 (UInt32.v desti) == Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) ==
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length #UInt8.t dest) ==
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length #UInt8.t dest)) ))

assume val memcpy_16: src:u16s -> srci:UInt32.t -> dest:u16s -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq h1 dest in let d0 = to_seq h0 dest in let s0 = to_seq h0 src in
        Seq.slice d1 0 (UInt32.v desti) == Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) ==
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) ==
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest) )))

assume val memcpy_32: src:u32s -> srci:UInt32.t -> dest:u32s -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq h1 dest in let d0 = to_seq h0 dest in let s0 = to_seq h0 src in
        Seq.slice d1 0 (UInt32.v desti) == Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) ==
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) ==
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest) )))

assume val memcpy_64: src:u64s -> srci:UInt32.t -> dest:u64s -> desti:UInt32.t -> len:UInt32.t ->
  STL unit 
  (requires (fun h -> live h src /\ live h dest /\ disjoint src dest 
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len))
  (ensures  (fun h0 _ h1 -> live h0 src /\ live h0 dest /\ live h1 dest /\ modifies_1 dest h0 h1
    /\ length src >= UInt32.v srci + UInt32.v len /\ length dest >= UInt32.v desti + UInt32.v len
    /\ (let d1 = to_seq h1 dest in let d0 = to_seq h0 dest in let s0 = to_seq h0 src in
        Seq.slice d1 0 (UInt32.v desti) == Seq.slice d0 0 (UInt32.v desti)
	/\ Seq.slice d1 (UInt32.v desti) (UInt32.v desti + UInt32.v len) ==
	    Seq.slice s0 (UInt32.v srci) (UInt32.v srci + UInt32.v len)
	/\ Seq.slice d1 (UInt32.v desti + UInt32.v len) (length dest) ==
	    Seq.slice d0 (UInt32.v desti + UInt32.v len) (length dest) )))

assume val sub_8: b:bytes -> i:UInt32.t -> len:UInt32.t{UInt32.v i + UInt32.v len <= length #UInt8.t b} -> STL bytes
  (requires (fun h -> live #UInt8.t h b))
  (ensures  (fun h0 b' h1 -> live #UInt8.t h0 b /\ live #UInt8.t h1 b' /\ includes b b' /\ h1 == h0
    /\ length #UInt8.t b' = UInt32.v len
    /\ to_seq #UInt8.t h1 b' == Seq.slice (to_seq #UInt8.t h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len) ))

assume val sub_16: b:u16s -> i:UInt32.t -> len:UInt32.t{UInt32.v i + UInt32.v len <= length b} -> STL u16s
  (requires (fun h -> live h b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = UInt32.v len
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len) ))

assume val sub_32: b:u32s -> i:UInt32.t -> len:UInt32.t{UInt32.v i + UInt32.v len <= length b} -> STL u32s
  (requires (fun h -> live h b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = UInt32.v len
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len) ))

assume val sub_64: b:u64s -> i:UInt32.t -> len:UInt32.t{UInt32.v i + UInt32.v len <= length b} -> STL u64s
  (requires (fun h -> live h b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = UInt32.v len
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len) ))

assume val offset_8: b:bytes -> i:UInt32.t{UInt32.v i <= length #UInt8.t b} -> STL bytes
  (requires (fun h -> live #UInt8.t h b))
  (ensures  (fun h0 b' h1 -> live #UInt8.t h0 b /\ live #UInt8.t h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length #UInt8.t b' = length #UInt8.t b - UInt32.v i
    /\ to_seq #UInt8.t h1 b' == Seq.slice (to_seq #UInt8.t h0 b) (UInt32.v i) (length #UInt8.t b) ))

assume val offset_16: b:u16s -> i:UInt32.t{UInt32.v i <= length b} -> STL u16s
  (requires (fun h -> live h b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = length b - UInt32.v i
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (length b) ))

assume val offset_32: b:u32s -> i:UInt32.t{UInt32.v i <= length b} -> STL u32s
  (requires (fun h -> live h b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = length b - UInt32.v i
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (length b) ))

assume val offset_64: b:u64s -> i:UInt32.t{UInt32.v i <= length b} -> STL u64s
  (requires (fun h -> live h b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = length b - UInt32.v i
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (length b) ))
