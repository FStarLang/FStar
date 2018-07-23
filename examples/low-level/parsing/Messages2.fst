module Messages2

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Int.Cast
open FStar.Buffer
open Low.Bytes

assume MaxInt8: pow2 8 = 256

(* Native types which have a "size_of" value *)
assume type hasSize (t:Type) : Type0
assume HasSizeUInt8 : hasSize UInt8.t
assume HasSizeUInt16: hasSize UInt16.t
assume HasSizeUInt32: hasSize UInt32.t
assume HasSizeUInt64: hasSize UInt64.t

(* Type of types that have a size *)
let sized_type = t:Type{hasSize t}
(* Associate the actual size to sized_types *)
assume val sizeof: t:sized_type -> Tot size
(* Serialized any sized_type into a sequence of (sizeof t) bytes *)
assume val flatten: #t:sized_type -> x:t -> Tot (s:Seq.seq UInt8.t{Seq.length s = sizeof t})
(* Inflates a sequence of (sizeof t) bytes into an object of sized_type t *)
assume val inflate: t:sized_type -> s:Seq.seq UInt8.t{Seq.length s = sizeof t} -> Tot t

(* Inflate and flatten are in bijection *)
assume FlattenBijective: forall (t:sized_type) (x:t).
  inflate t (flatten #t x) == x

(* Assumed sizeof values for native types *)
assume SizeOfU8:  sizeof UInt8.t = 1
assume SizeOfU16: sizeof UInt16.t = 2
assume SizeOfU32: sizeof UInt32.t = 4
assume SizeOfU64: sizeof UInt64.t = 8

(* Assumed flatten values for native types *)
(* The injectivity of flatten is most of what we should need anyway *)
assume FlattenU8: flatten #UInt8.t == (fun (x:UInt8.t) -> Seq.create 1 x)
assume FlattenU16: flatten #UInt16.t == (fun (x:UInt16.t) -> let s = Seq.create 2 0uy in
							   let s = Seq.upd s 0 (uint16_to_uint8 x) in
							   let s = Seq.upd s 1 (uint16_to_uint8 (UInt16.shift_right x 8ul)) in
							   s)
(*
  assume Flatten ...
*)

(* Yet another definition of buffer 'a:.
   Basically a buffer of bytes that must be interpreted as a buffer of type t *)
type buffer (t:sized_type) = b:bytes{length b % sizeof t = 0}

(* Function to cast pointers into other pointer types *)
val ptr_cast: #t:sized_type -> t':sized_type -> b:buffer t{length b % sizeof t' = 0} -> Tot (b':buffer t')
let ptr_cast #t t' b = 
  let b':bytes = b in b'

(* Another definition of the length of such buffers *)
let length #t (b:buffer t) = Buffer.length b / sizeof t
let idx #t (b:buffer t) = Buffer.idx b / sizeof t

(* From a 'buffer t', returns a 'seq t', needed to define operations on buffers *)
(* To seq is basically implemented using a sequence of inflated values *)
assume val to_seq: #a:sized_type -> h:mem -> b:buffer a -> 
  GTot (s:Seq.seq a{Seq.length s = length b})
(* let to_seq #a h b = *)
(*   let seq_bytes = as_seq h b in *)
(*   let rec mk_seq_a (s:Seq.seq UInt8.t) : Tot (s':Seq.seq a) (decreases (Seq.length s)) = *)
(*     if Seq.length s = 0 then Seq.empty #a *)
(*     else Seq.append #a (mk_seq_a (Seq.slice s (sizeof a) (Seq.length s))) (Seq.create 1 (inflate a (Seq.slice s 0 (sizeof a)))) in *)
(*   mk_seq_a seq_bytes *)

(* Crucial properties for proofs *)
assume val lemma_to_seq_is_injective: #a:sized_type -> h:mem -> b:buffer a -> h':mem -> b':buffer a ->
  Lemma
  (requires (True))
  (ensures ((to_seq h b == to_seq h' b') <==> Buffer.equal h b h' b'))
  [SMTPat (to_seq h b); SMTPat (to_seq h' b')]

(* Buffers also have (fixed) size. 8 as I consider these are 64bit pointers *)
assume HasSizeBuffer: forall (a:sized_type). hasSize (buffer a)
assume SizeOfBuffer: forall (a:sized_type) . sizeof (buffer a) = 8

(* Stateful functions on buffers *)
assume val create: t:sized_type -> len:UInt32.t -> ST (buffer t)
  (requires (fun h -> True))
  (ensures  (fun h0 b h1 -> modifies_0 h0 h1 /\ live h1 b /\ ~(contains h0 b) /\ frameOf b = h0.tip))

assume val read: #a:sized_type -> b:buffer a -> i:UInt32.t{UInt32.v i < length b} -> STL a
  (requires (fun h -> live h b))
  (ensures  (fun h0 z h1 -> h1 == h0 /\ live h0 b /\ z == Seq.index (to_seq h0 b) (UInt32.v i)))

assume val write: #a:sized_type -> b:buffer a -> i:UInt32.t{UInt32.v i < length b} -> z:a -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ to_seq h1 b == Seq.upd (to_seq h0 b) (UInt32.v i) z))

assume val offset: #t:sized_type -> b:buffer t -> i:UInt32.t -> STL (buffer t)
  (requires (fun h -> live h b /\ UInt32.v i <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ idx b' = idx b + UInt32.v i /\ length b' = length b - UInt32.v i
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (length b) ))

assume val sub: #t:sized_type -> b:buffer t -> i:UInt32.t -> len:UInt32.t -> STL (buffer t)
  (requires (fun h -> live h b /\ UInt32.v i + UInt32.v len <= length b))
  (ensures  (fun h0 b' h1 -> live h0 b /\ live h1 b' /\ includes b b' /\ h1 == h0
    /\ UInt32.v i + UInt32.v len <= length b
    /\ idx b' = idx b + UInt32.v i /\ length b' = UInt32.v len
    /\ to_seq h1 b' == Seq.slice (to_seq h0 b) (UInt32.v i) (UInt32.v i + UInt32.v len)
    ))

assume val memcpy: #t:sized_type -> src:buffer t -> srci:UInt32.t -> dest:buffer t -> desti:UInt32.t -> len:UInt32.t ->
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

(* Specific types for parsing *)

(* The base buffer type *)
let bytes = buffer UInt8.t

(* Buffer which size is known *)
let buf (t:sized_type) (n:nat) = b:buffer UInt8.t{Buffer.length b = sizeof t * n}

assume HasSizeBuf: forall (a:sized_type) (n:nat). hasSize (buf a n)
assume SizeOfBuf: forall (a:sized_type) (n:nat). sizeof (buf a n) = 8

(* Buffer of variable length, encoded in the record *)
(* It is encoded as a reference, could also be encoded as a seq, or anything "by value" *)
noeq type buf_var (len_bytes:nat) (t:sized_type) =
  {b_length: buf UInt8.t len_bytes;
   b_content: bytes}

assume HasSizeBufVar: forall (len_bytes:nat) (t:sized_type). hasSize (buf_var len_bytes t)
assume SizeOfBufVar: forall (len_bytes:nat) (t:sized_type). sizeof (buf_var len_bytes t) = sizeof (buf UInt8.t len_bytes) + sizeof bytes

(* Similar to the previous, but is content points to a buffer t and not bytes *)
noeq type arraybuf_var (len_bytes:nat) (a:sized_type) =
     {abv_length: buf UInt8.t len_bytes;
      abv_content: buffer a}

assume HasSizeArrayBufVar: forall (len_bytes:nat) (t:sized_type). hasSize (arraybuf_var len_bytes t)
assume SizeOfArrayBufVar: forall (len_bytes:nat) (t:sized_type). 
  sizeof (arraybuf_var len_bytes t) = sizeof (buf UInt8.t len_bytes) 
    + sizeof (buffer t)

(* Type of variable length buffers for which we preallocated some fixed size space.
   Hence the corresponding buffer must have a bounded length *)
(* assume new type arraybuf (len_bytes:nat) (a:sized_type) (max:pos) *)
noeq type arraybuf (len_bytes:nat) (a:sized_type) (max:pos) =
  {ab_length: buf UInt8.t len_bytes;
   ab_content:s:Seq.seq a{Seq.length s = max}}

assume HasSizeArrayBuf: forall (len_bytes:nat) (t:sized_type) (max:pos). hasSize (arraybuf len_bytes t max)
assume SizeOfArrayBuf: forall (len_bytes:nat) (t:sized_type) (max:pos). 
  sizeof (arraybuf_var len_bytes t) = sizeof (buf UInt8.t len_bytes) 
    + max * sizeof t // Max size of the payload. E.g 256 * 8 bytes for 


(* Other types, should be somehow generated automatically *)

noeq type key_share = {
  ks_group_name: buf UInt16.t 1;
  ks_public_key: buf_var 1 UInt8.t
}

(* Ideally that would be automatic *)
assume HasSizeKeyShare: hasSize key_share
assume SizeOfKeyShare: sizeof key_share = sizeof (buf UInt16.t 1) + sizeof (buf_var 1 UInt8.t)

noeq type client_extension =
 | CE_extended_ms
 | CE_secure_renegotiation of buf_var 1 UInt8.t
 | CE_supported_groups of buf_var 2 UInt16.t
 | CE_supported_point_formats of buf_var 1 UInt8.t
 | CE_signature_algorithms of buf_var 2 UInt16.t
 | CE_earlyData
 | CE_keyShare of arraybuf_var 2 key_share
 | CE_preSharedKey of arraybuf_var 2 (buf_var 2 UInt8.t)
 | CE_server_names of arraybuf_var 2 (buf_var 2 UInt8.t)
 (* | CE_server_names of arraybuf 2 (buf_var 2 UInt8.t) 128 *)

let max x y = if x < y then y else x

assume HasSizeClientExtension: hasSize client_extension
assume SizeOfClientExtension: sizeof client_extension = 1 (* The type for instance *)
  + max (max (max (sizeof (buf_var 1 UInt8.t)) (sizeof (buf_var 2 UInt8.t)))
	     (max (sizeof (buf_var 2 UInt16.t)) (sizeof (buf_var 1 UInt8.t))))
	 (max (max (sizeof (arraybuf_var 2 key_share)) (sizeof (arraybuf_var 2 (buf_var 2 UInt8.t))))
              (sizeof (arraybuf_var 2 (buf_var 2 UInt8.t))))

noeq type ch =  {
  ch_protocol_version:buf UInt16.t 1;
  ch_client_random:buf UInt8.t 32;
  ch_sessionID:buf_var 1 UInt8.t;
  ch_cipher_suites:buf_var 2 UInt16.t;
  ch_compressions:buf_var 1 UInt8.t;
  ch_extensions:arraybuf_var 2 client_extension;
}

assume HasSizeClientHello: hasSize ch
assume SizeOfClientHello: sizeof ch = sizeof (buf UInt16.t 1)
				      + sizeof (buf UInt8.t 32)
				      + sizeof (buf_var 1 UInt8.t)
				      + sizeof (buf_var 2 UInt16.t)
				      + sizeof (buf_var 1 UInt8.t)
				      + sizeof (arraybuf_var 2 client_extension)
