module FStar.ImmBuffer

open FStar.Seq
open FStar.UInt8
open FStar.UInt32
open FStar.Ghost
open FStar.Int.Cast

(** **************************************************************** **)
(** Defining a generic 'bytes' type as a view on a sequence of bytes **)
(** **************************************************************** **)
assume MaxUInt32: pow2 32 = 4294967296

let lemma_size (x:int) : Lemma (requires (UInt.size x n))
				     (ensures (x >= 0))
				     [SMTPat (UInt.size x n)]
  = ()

(* TODO: leaving sequences bounded for the moment *)
type bounded_seq (t:Type) = s:seq t{length s <= UInt.max_int n}

(* Immutable buffer type *)
noeq private type bytes' = {
  content: bounded_seq byte;
  start: UInt32.t;
  length: UInt32.t;
}

type bytes = b:bytes'{length b.content >= v b.start + v b.length}

let bytes_length b : Tot nat = v b.length
let g_bytes_length b : Tot (erased nat) = hide (v b.length)

let bytes_idx b : Tot nat = v b.start
let g_idx b : Tot (erased nat) = hide (v b.start)

let content b : Tot (bounded_seq byte) = b.content
let g_content b : Tot (erased (bounded_seq byte)) = hide b.content

let as_seq (b:bytes) : Tot (bounded_seq byte) = Seq.slice b.content (v b.start) (v b.start + v b.length)

let get_byte (b:bytes) (i:nat{i < bytes_length b}) : Tot byte = Seq.index (as_seq b) i

(* Equality predicate on bytes *)
let equal_bytes b b' : Tot Type0 = as_seq b == as_seq b'

(* TODO: introduce lemmas about the equality for quantifiers *)
let lemma_eq_intro (b:bytes) (b':bytes) : Lemma
  (requires (bytes_length b = bytes_length b' /\ (forall (i:nat). i < bytes_length b ==> get_byte b i = get_byte b' i)))
  (ensures  (equal_bytes b b')) =
    Seq.lemma_eq_intro (as_seq b) (as_seq b')

(* TODO: Tot or Tot ? 
   Maybe for immutable bytes they should always be received from 
   the outside, e.g. TCP buffer *)
let create_bytes (len:t) : Tot bytes =
  {content = Seq.create (v len) 0uy; start = 0ul; length = len}
let index_bytes (b:bytes) (i:t{v i < bytes_length b}) : Tot byte = 
  Seq.index (Seq.slice b.content (v b.start) (v b.start + v b.length)) (v i)
let sub_bytes (b:bytes) (i:t) (len:t{v i + v len <= bytes_length b}) : Tot bytes =
  {content = b.content; length = b.length -^ i -^ len; start = b.start +^ i}
let offset_bytes (b:bytes) (i:t{v i <= bytes_length b}) : Tot bytes =
  {content = b.content; length = b.length -^ i; start = b.start +^ i}
let split_bytes (b:bytes) (i:t{v i <= bytes_length b}) : Tot (bytes * bytes) =
  sub_bytes b 0ul i, offset_bytes b i
let of_seq (s:bounded_seq byte) : Tot bytes =
  {content = s; start = 0ul; length = uint_to_t (Seq.length s)}

(** **************************************************************** **)
(**                    Defining serializable types                   **)
(** **************************************************************** **)

assume type hasSize (t:Type) : Type0
assume val sizeof: t:Type{hasSize t} -> Tot pos

(* Native machine types have a size *)
assume HasSizeUInt8 : hasSize UInt8.t
assume HasSizeUInt16: hasSize UInt16.t
assume HasSizeUInt32: hasSize UInt32.t
assume HasSizeUInt64: hasSize UInt64.t
assume HasSizeBytes:  hasSize  bytes

assume SizeOfU8:  sizeof UInt8.t = 1
assume SizeOfU16: sizeof UInt16.t = 2
assume SizeOfU32: sizeof UInt32.t = 4
assume SizeOfU64: sizeof UInt64.t = 8
assume SizeOfByes: sizeof bytes = 8

type serializer (#t:Type{hasSize t}) = x:t -> Tot (s:seq byte{Seq.length s = sizeof t})
let inj_serializer (#t:Type{hasSize t}) = s:serializer #t{forall (x:t) (y:t). s x == s y ==> x == y}

type serializable (t:Type0{hasSize t}) ($f:inj_serializer #t) = (t:Type0)
type buffer (#t:Type0{hasSize t}) (#f:inj_serializer) (ty:serializable t f) = b:bytes{bytes_length b % sizeof t = 0}

type pinverse_t (#a:Type) (#b:Type) ($f:(a -> Tot b)) = b -> Tot (result a)

let coerce (#t:Type{hasSize t}) (f:inj_serializer #t) : Tot (g:(t -> Tot (seq byte))) = f

assume val inv: #t:Type{hasSize t} -> f:inj_serializer #t -> Tot (pinverse_t #t #(seq byte) (coerce f))

(* inline type lemma_inverse_g_f (#a:Type) (#b:Type) ($f:a -> Tot b) ($g:b -> Tot (result a)) (x:a) = *)
(*   g (f x) = Correct x *)

(* inline type lemma_pinverse_f_g (#a:Type) (#b:Type) (r:b -> b -> Type) ($f:a -> Tot b) ($g:b -> Tot (result a)) (y:b) = *)
(*   is_Correct (g y) ==> r (f (Correct._0 (g y))) y *)

let length (#t:Type0{hasSize t}) (#f:inj_serializer) (#ty:serializable t f) (b:buffer ty) = bytes_length b / sizeof t

let idx (#t:Type0{hasSize t}) (#f:inj_serializer) (#ty:serializable t f) (b:buffer ty) = bytes_idx b / sizeof t

val read: #t':Type0{hasSize t'} -> #f:inj_serializer #t' -> #ty:serializable t' f -> 
  b:buffer ty -> i:t{v i < length b} -> Tot ty
let read #t (#f:inj_serializer #t) #ty b i = 
  admit(); // TODO
  (inv f) (slice (as_seq b) (idx b + v i) (idx b + v i + sizeof t))

val sub: #t':Type0{hasSize t'} -> #f:inj_serializer #t' -> #ty:serializable t' f -> 
  b:buffer ty -> i:t -> j:t{v i + v j <= length b} -> Tot (buffer ty)
let sub #t (#f:inj_serializer #t) #ty b i j =
  admit(); // TODO
  sub_bytes b (uint_to_t (sizeof t) *^ i) (uint_to_t (sizeof t) *^ j)

val offset: #t':Type0{hasSize t'} -> #f:inj_serializer #t' -> #ty:serializable t' f -> 
  b:buffer ty -> i:t{v i <= length b} -> Tot (buffer ty)
let offset #t (#f:inj_serializer #t) #ty b i =
  admit(); // TODO
  offset_bytes b (uint_to_t (sizeof t) *^ i)

noeq type buffer_tuple =  {
    fst: bytes;
    snd: bytes
  }

val split: #t':Type0{hasSize t'} -> #f:inj_serializer #t' -> #ty:serializable t' f -> 
  b:buffer ty -> i:t{v i <= length b} -> Tot buffer_tuple
let split #t (#f:inj_serializer #t) #ty b i =
  admit()(* ; // TODO *)
  (* {fst = sub b 0ul; snd = i offset b i} *)

assume val le_uint16_serializer: inj_serializer #UInt16.t
(* let le_uint16_serializer = admit(); *)
(*   fun s -> let open FStar.UInt16 in *)
(* 	 let s0 = uint16_to_uint8 s in *)
(* 	 let s1 = uint16_to_uint8 (s >>^ 8ul)  in *)
(* 	 (Seq.create 1 s0) @| (Seq.create 1 s1) *)

assume val le_uint32_serializer: inj_serializer #UInt32.t
(* let le_uint32_serializer = *)
(*   admit(); *)
(*   fun s -> let open FStar.UInt32 in *)
(* 	 let s0 = uint32_to_uint8 s in *)
(* 	 let s1 = uint32_to_uint8 (s >>^ 8ul)  in *)
(* 	 let s2 = uint32_to_uint8 (s >>^ 16ul)  in *)
(* 	 let s3 = uint32_to_uint8 (s >>^ 24ul)  in *)
(* 	 (Seq.create 1 s0) @| (Seq.create 1 s1) @| (Seq.create 1 s2) @| (Seq.create 1 s3) *)

(* TODO: add more of those functions and prove them injective *)

type uint16 = serializable UInt16.t (le_uint16_serializer)
type uint32 = serializable UInt32.t (le_uint32_serializer)
