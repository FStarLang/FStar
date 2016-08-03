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
type bounded_seq (t:Type0) = s:seq t{length s <= UInt.max_int n}

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

let as_seq_bytes (b:bytes) : Tot (bounded_seq byte) = Seq.slice b.content (v b.start) (v b.start + v b.length)

let get_byte (b:bytes) (i:nat{i < bytes_length b}) : Tot byte = Seq.index (as_seq_bytes b) i

(* Equality predicate on bytes *)
let equal_bytes b b' : Tot Type0 = as_seq_bytes b == as_seq_bytes b'

(* TODO: introduce lemmas about the equality for quantifiers *)
let lemma_eq_intro (b:bytes) (b':bytes) : Lemma
  (requires (bytes_length b = bytes_length b' /\ (forall (i:nat). i < bytes_length b ==> get_byte b i = get_byte b' i)))
  (ensures  (equal_bytes b b')) =
    Seq.lemma_eq_intro (as_seq_bytes b) (as_seq_bytes b')

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

assume val of_string': str:string -> Tot (s:seq byte{Seq.length s = String.length str})
let of_string (s:string{String.length s < pow2 32}) : Tot bytes = 
  {content = of_string' s; start = 0ul; length = uint_to_t (String.length s)}

(** **************************************************************** **)
(**           Defining serializable types of fixed length            **)
(** **************************************************************** **)

open FStar.Mul

type result 'a : Type0 =
  | Correct of 'a
  | Error of string

let correct (#a:Type) (r:result a{is_Correct r}) : Tot a = match r with | Correct x -> x

assume type hasSize (t:Type0) : Type0
type sizeof_t = t:Type0{hasSize t}
assume val sizeof: t:sizeof_t -> Tot (z:UInt.uint_t n{z > 0})

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

type injective (#a:Type) (#b:Type) (f:a -> Tot b) =
  forall (x:a) (y:a). f x == f y ==> x == y

(* Type of functions that turn F* types into sequences of bytes *)
type serializer (t:sizeof_t) =
  f:(t -> Tot (s:seq byte{Seq.length s = sizeof t})){injective f}

(* Type of the inverse of the serialization *)
type parser (#t:sizeof_t) ($f:serializer t) =
  seq byte -> Tot (result t)

(* Type of F* types that can be serialized into sequences of bytes *)
type inverse (#t:sizeof_t) ($f:serializer t) ($g:parser f) =
  (forall (x:t). g (f x) == Correct x) /\ (forall (y:seq byte). is_Correct (g y) ==>  (f (Correct._0 (g y))) == y)

noeq type serializable (t:sizeof_t) : Type0 =
| Serializable: $f:serializer t -> $g:parser f{inverse f g} -> serializable t

assume val lemma_aux_0: x:nat -> y:pos -> Lemma
  (requires (x > 0 /\ x % y = 0))
  (ensures  (x - y >= 0 /\ (x - y) % y = 0))

val of_seq_bytes: #t:sizeof_t -> #ty:serializable t  ->
  s:Seq.seq byte{Seq.length s % sizeof t = 0} ->
  Tot (result (s':Seq.seq t))
  (decreases (Seq.length s))
let rec of_seq_bytes #t #ty s =
  let Serializable serialize parse = ty in
  if Seq.length s = 0 then Correct (Seq.createEmpty #t)
  else begin
    lemma_aux_0 (Seq.length s) (sizeof t);
    let a = parse (Seq.slice s 0 (sizeof t)) in
    let b = of_seq_bytes (Seq.slice s (sizeof t) (Seq.length s)) in
    match a,b with
    | Correct x, Correct y ->
      Correct (Seq.append (Seq.create 1 x) y)
    | _, _ -> Error ""
  end

val to_seq_bytes: #t:sizeof_t -> #ty:serializable t -> s:Seq.seq t ->
  Tot (s':Seq.seq byte)
  (decreases (Seq.length s))
let rec to_seq_bytes #t #ty s =
  let Serializable serialize parse = ty in
  if Seq.length s = 0 then Seq.createEmpty #UInt8.t
  else Seq.append (serialize (Seq.index s 0)) (to_seq_bytes (Seq.slice s 1 (Seq.length s)))

(* Buffer of serializable types *)
(* It is a "flat" representation of some structures in memory *)
type buffer (#t:sizeof_t) (ty:serializable t) =
  b:bytes{bytes_length b % sizeof t = 0
   /\  is_Correct (of_seq_bytes #t #ty (as_seq_bytes b))}

assume BufferHasSize: forall (#ty:sizeof_t) (t:serializable ty).
  hasSize (buffer t) /\ sizeof (buffer t) = sizeof (bytes)

let length (#t:sizeof_t) (#ty:serializable t) (b:buffer ty) = bytes_length b / sizeof t

let idx (#t:sizeof_t) (#ty:serializable t) (b:buffer ty) = bytes_idx b / sizeof t

let as_seq (#t:sizeof_t) (#ty:serializable t) (b:buffer ty) : Tot (s:seq t) =
  let Serializable f g = ty in
  let s = as_seq_bytes b in
  let s = of_seq_bytes  #t #ty s in
  match s with | Correct x -> x

assume val lemma_as_seq_length: #t:sizeof_t -> #ty:serializable t -> b:buffer ty -> Lemma
  (requires (True))
  (ensures  (Seq.length (as_seq #t #ty b) = length b))
  [SMTPat ((as_seq #t #ty b))]

assume val lemma_as_seq_inj: #t:sizeof_t -> #ty:serializable t -> b:buffer ty -> b':buffer ty -> Lemma
  (requires (as_seq #t #ty b == as_seq #t #ty b'))
  (ensures  (equal_bytes b b'))
  (* [SMTPat (equal_bytes b b')] *)

val read: #t':sizeof_t -> #ty:serializable t' -> 
  b:buffer ty -> i:t{v i < length b} -> Tot t'
let read #t #ty b i =
  Seq.index (as_seq #t #ty b) (v i)

val sub: #t':sizeof_t -> #ty:serializable t' -> 
  b:buffer ty -> i:t -> j:t{v i + v j <= length b} -> 
  Tot (b':buffer ty{length b' = v j /\ as_seq b' == Seq.slice (as_seq b) (v i) (v i + v j)})
let sub #t #ty b i j =
  admit(); // TODO
  sub_bytes b (uint_to_t (sizeof t) *^ i) (uint_to_t (sizeof t) *^ j)

val offset: #t':sizeof_t -> #ty:serializable t' -> 
  b:buffer ty -> i:t{v i <= length b} -> 
  Tot (b':buffer ty{length b' = length b - v i /\ as_seq b' == Seq.slice (as_seq b) (v i) (length b)})
let offset #t #ty b i =
  admit(); // TODO
  offset_bytes b (uint_to_t (sizeof t) *^ i)

noeq type buffer_tuple (#t':sizeof_t) (ty:serializable t') =  {
    fst: buffer ty;
    snd: buffer ty
  }

(* There should be a "sizeof" calculus to compute that automatically on record types *)
assume BufferTupleHasSize: forall (t':sizeof_t) (ty:serializable t'). 
  hasSize (buffer_tuple ty) /\ sizeof (buffer_tuple ty) = sizeof (buffer ty) + sizeof (buffer ty)

val split: #t':sizeof_t -> #ty:serializable t' -> 
  b:buffer ty -> i:t{v i <= length b} -> Tot (buffer_tuple ty)
let split #t #ty b i =
  let fst = sub b 0ul i in
  let snd = offset b i in
  {fst = fst; snd = snd}

(* Cast a "buffer type" to its unrefined "bytes" type *)
let to_bytes (#t:sizeof_t) (#ty:serializable t) (b:buffer ty)
  : Tot bytes
  = b

(* Cast an appropriate "bytes" object to the corresponding "buffer " type *)
let to_buffer (#t:sizeof_t) (ty:serializable t) (b:bytes{bytes_length b % sizeof t = 0
  /\ is_Correct (of_seq_bytes #t #ty (as_seq_bytes b))})
  : Tot (buffer ty)
  = b

(* Generic cast function to cast pointers of one type into pointers of another type *)
(* Mostly for casts between native low level types (machine ints and pointers*)
let cast (#t:sizeof_t) (ty:serializable t) (#t':sizeof_t) (#ty':serializable t') 
  (b:buffer ty'{bytes_length (to_bytes b) % sizeof t = 0
   /\ is_Correct (of_seq_bytes #t #ty (as_seq_bytes b))})
  : Tot (b':buffer ty) = to_buffer #t ty (to_bytes b)

val le_uint8_serializer: serializer byte
let le_uint8_serializer =
  let f:b:byte -> Tot (s:seq byte{Seq.length s = sizeof byte}) = 
    (fun s -> Seq.create 1 s) in
  assume(injective f); 
  f

val le_uint8_parser: parser le_uint8_serializer
let le_uint8_parser =
  let f: s:seq byte -> Tot (result byte) =
    fun s -> if Seq.length s = 1 then Correct (index s 0)
		       else Error "Too long or too short" in
  f

val le_uint16_serializer: serializer UInt16.t
let le_uint16_serializer =
  let f:b:UInt16.t -> Tot (s:seq byte{Seq.length s = sizeof UInt16.t}) =
    fun s ->
      let open FStar.UInt16 in
      let s0 = uint16_to_uint8 s in
      let s1 = uint16_to_uint8 (s >>^ 8ul)  in
      (Seq.create 1 s0) @| (Seq.create 1 s1) in
   assume (injective f);
   f

val le_uint16_parser : (* p: *)(parser #UInt16.t (le_uint16_serializer))(* {inverse le_uint16_serializer p} *)
let le_uint16_parser =
  fun (s:seq byte) ->
    if Seq.length s = 2 then Correct (
      let open FStar.UInt16 in
      uint8_to_uint16 (Seq.index s 0) +^ (uint8_to_uint16 (Seq.index s 1)) <<^  8ul
    )
    else Error "Too short"

assume val le_uint8_lemma:  unit -> Lemma
  (inverse #UInt8.t le_uint8_serializer le_uint8_parser)
assume val le_uint16_lemma:  unit -> Lemma
  (inverse #UInt16.t le_uint16_serializer le_uint16_parser)

assume val ptr_serializer: serializer bytes
assume val ptr_parser: p:parser ptr_serializer{inverse ptr_serializer p}

val le_uint8_parser': p:(parser #UInt8.t (le_uint8_serializer)){inverse le_uint8_serializer p}
let le_uint8_parser' = le_uint8_lemma (); le_uint8_parser

val le_uint16_parser': p:(parser #UInt16.t (le_uint16_serializer)){inverse le_uint16_serializer p}
let le_uint16_parser' = le_uint16_lemma (); le_uint16_parser

let u8  : serializable byte     = Serializable le_uint8_serializer  le_uint8_parser'
let u16 : serializable UInt16.t = Serializable le_uint16_serializer le_uint16_parser'

let ptr = Serializable ptr_serializer ptr_parser


(* let uint16s = buffer #UInt16.t #le_uint16_serializer uint16 *)

(* assume val le_uint32_serializer: serializer UInt32.t *)
(* let le_uint32_serializer = *)
(*   admit(); *)
(*   fun s -> let open FStar.UInt32 in *)
(* 	 let s0 = uint32_to_uint8 s in *)
(* 	 let s1 = uint32_to_uint8 (s >>^ 8ul)  in *)
(* 	 let s2 = uint32_to_uint8 (s >>^ 16ul)  in *)
(* 	 let s3 = uint32_to_uint8 (s >>^ 24ul)  in *)
(* 	 (Seq.create 1 s0) @| (Seq.create 1 s1) @| (Seq.create 1 s2) @| (Seq.create 1 s3) *)

(* let uint32: Type0 =  *)
(*   let s:Type0 = serializable UInt32.t (le_uint32_serializer)  in s *)

(*
noeq type key_share_ = {a:bytes; b:bytes}
assume HasSizeKeyShare : hasSize key_share_
assume HasSizeKeyShare' : sizeof key_share_ = 3
assume val serialize_key_share: inj_serializer key_share_ //seq byte -> Tot key_share_
assume val parse_key_share: pinverse_t  (coerce serialize_key_share)

let key_share = serializable key_share_ serialize_key_share
*)

(* let ty = buffer (\* #key_share_ #serialize_key_share  *\)key_share *)
