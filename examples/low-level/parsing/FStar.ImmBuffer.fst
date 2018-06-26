module ImmBuffer

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
(* type bounded_seq (t:Type0) = s:seq t{length s <= UInt.max_int n} *)

(* Immutable buffer type *)
noeq private type bytes' = {
  (* content: bounded_seq byte; *)
  content: seq byte;
  start: UInt32.t;
  length: UInt32.t;
}

(* Valid "bytes" *)
type bytes = b:bytes'{UInt.size (v b.start + v b.length) n /\  length b.content >= v b.start + v b.length}

(* Operators to manipulate bytes. NB those are read only, hence no update or create functions *)
let length_bytes (b:bytes) : Tot nat = v b.length
let start_bytes  (b:bytes) : Tot nat = v b.start
let content_bytes (b:bytes) : Tot (seq byte) = b.content
let index_bytes (b:bytes) (i:t{v i < length_bytes b}) : Tot byte = 
  Seq.index (Seq.slice b.content (v b.start) (v b.start + v b.length)) (v i)
let sub_bytes (b:bytes) (i:t) (len:t{v i + v len <= length_bytes b}) : Tot bytes =
  {content = b.content; length = len; start = b.start +^ i}
let offset_bytes (b:bytes) (i:t{v i <= length_bytes b}) : Tot bytes =
  {content = b.content; length = b.length -^ i; start = b.start +^ i}
let split_bytes (b:bytes) (i:t{v i <= length_bytes b}) : Tot (bytes * bytes) =
  sub_bytes b 0ul i, offset_bytes b i
let to_seq_byte (b:bytes) : Tot (seq byte) = Seq.slice b.content (start_bytes b) (start_bytes b + length_bytes b)
let of_seq_byte (s:seq byte{Seq.length s < pow2 32}) : Tot bytes =
  {content = s; start = 0ul; length = uint_to_t (Seq.length s)}
let of_string (s:string) : Tot bytes = magic() // TOOD

(* Equality predicate on bytes *)
let equal_bytes b b' : GTot Type0 = to_seq_byte b == to_seq_byte b'
let lemma_eq_intro (b:bytes) (b':bytes) : Lemma
  (requires (length_bytes b = length_bytes b' /\ (forall (i:nat). i < length_bytes b ==> index_bytes b (uint_to_t i) == index_bytes b' (uint_to_t i))))
  (ensures  (equal_bytes b b')) =
    Seq.lemma_eq_intro (to_seq_byte b) (to_seq_byte b')

(** **************************************************************** **)
(**           Defining serializable types of fixed length            **)
(** **************************************************************** **)

open FStar.Mul

(* Optional results for the parsing functions *)
type result 'a : Type0 =
  | Correct of 'a
  | Error of string

(* Destructors for that type *)
let correct (#a:Type) (r:result a{Correct? r}) : Tot a = match r with | Correct x -> x
let errror (#a:Type) (r:result a{Error? r}) : Tot string = match r with | Error s -> s

(* Size predicate, for types on which one can compute "sizeof" as in C *)
assume type hasSize (t:Type0) : Type0
type sizeof_t = t:Type0{hasSize t}
(* Equivalent of the C "sizeof" function *)
assume val sizeof: t:sizeof_t -> Tot (z:UInt.uint_t n{z > 0})

(* Native machine types have a size *)
assume HasSizeUInt8 : hasSize UInt8.t /\ sizeof UInt8.t = 1
assume HasSizeUInt16: hasSize UInt16.t /\ sizeof UInt16.t = 2
assume HasSizeUInt32: hasSize UInt32.t /\ sizeof UInt32.t = 4
assume HasSizeUInt64: hasSize UInt64.t /\ sizeof UInt64.t = 8
assume HasSizeBytes:  hasSize bytes /\ sizeof bytes = 8

(* Type of injective functions *)
type injective (#a:Type) (#b:Type) (f:a -> Tot b) : Type0 =
  forall (x:a) (y:a). f x == f y ==> x == y

type constant_size (#a:Type) (n:pos) (f:a -> Tot (seq byte)) : Type0 =
  forall (x:a). Seq.length (f x) = n

(* Type of functions that turn F* types into sequences of bytes *)
type serializer (t:sizeof_t) =
  f:(t -> Tot (s:seq byte)){injective f /\ constant_size (sizeof t) f }

(* Type of the inverse of the serialization *)
type parser (#t:sizeof_t) ($f:serializer t) =
  seq byte -> Tot (result t)

(* Type of F* types that can be serialized into sequences of bytes *)
type inverse (#t:sizeof_t) ($f:serializer t) ($g:parser f) =
  (forall (x:t). g (f x) == Correct x) /\ (forall (y:seq byte). Correct? (g y) ==>  (f (Correct._0 (g y))) == y)

noeq type serializable (t:sizeof_t) : Type0 =
| Serializable: $f:serializer t -> $g:parser f{inverse f g} -> serializable t

assume val lemma_aux_0: x:nat -> y:pos -> Lemma
  (requires (x > 0 /\ x % y = 0))
  (ensures  (x - y >= 0 /\ (x - y) % y = 0))

val of_seq_bytes: #t:sizeof_t -> #ty:serializable t  ->
  s:Seq.seq byte{Seq.length s % sizeof t = 0} ->
  Tot (result (s':Seq.seq t)) (decreases (Seq.length s))
let rec of_seq_bytes #t #ty s =
  let Serializable serialize parse = ty in
  if Seq.length s = 0 then Correct (Seq.empty #t)
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
  Tot (s':Seq.seq byte) (decreases (Seq.length s))
let rec to_seq_bytes #t #ty s =
  let Serializable serialize parse = ty in
  if Seq.length s = 0 then Seq.empty #UInt8.t
  else Seq.append (serialize (Seq.index s 0)) (to_seq_bytes (Seq.slice s 1 (Seq.length s)))

(* Buffer of serializable types *)
(* It is a "flat" representation of some structures in memory *)
let buffer (#t:sizeof_t) (ty:serializable t) = 
  b:bytes{length_bytes b % sizeof t = 0 /\ Correct? (of_seq_bytes #t #ty (to_seq_byte b))}

(* Buffer have the size of bytes (should infered using the types) *)
assume BufferHasSize: forall (#ty:sizeof_t) (t:serializable ty).
  hasSize (buffer t) /\ sizeof (buffer t) = sizeof (bytes)

val start: #t:sizeof_t -> #ty:serializable t -> b:buffer ty -> GTot nat
let start #t #ty b = start_bytes b

assume val length: #t:sizeof_t -> #ty:serializable t -> b:buffer ty -> GTot nat
assume BLengthDef: forall (t:sizeof_t) (ty:serializable t) (b:buffer ty).
  length_bytes b = sizeof t * length b

let to_seq (#t:sizeof_t) (#ty:serializable t) (b:buffer ty) : Tot (s:seq t) =
  let Serializable f g = ty in
  let s = to_seq_byte b in
  let s = of_seq_bytes #t #ty s in
  match s with | Correct x -> x

assume val lemma_as_seq_length: #t:sizeof_t -> #ty:serializable t -> b:buffer ty -> Lemma
  (requires (True))
  (ensures  (Seq.length (to_seq #t #ty b) = length b))
  [SMTPat ((to_seq #t #ty b))]

assume val lemma_as_seq_inj: #t:sizeof_t -> #ty:serializable t -> b:buffer ty -> b':buffer ty -> Lemma
  (requires (to_seq #t #ty b == to_seq #t #ty b'))
  (ensures  (equal_bytes b b'))
  (* [SMTPat (equal_bytes b b')] *)

(* All those functions are functionaly expressed in terms of 'to_seq', which hide the 
   concrete type layout *)
val read: #t':sizeof_t -> #ty:serializable t' -> b:buffer ty -> i:t{v i < length b} ->
  Tot (z:t'{z == index (to_seq b) (v i)})
let read #t' #ty b i = Seq.index (to_seq b) (v i)

assume val sub: #t':sizeof_t -> #ty:serializable t' -> 
  b:buffer ty -> i:t -> j:t{v i + v j <= length b} -> 
  Tot (b':buffer ty{
    start b' = start b + (sizeof t' * v i)
    /\ length b' = v j 
    /\ to_seq b' == Seq.slice (to_seq b) (v i) (v i + v j)})
(* let sub #t' #ty b i j = *)
(*   let size = uint_to_t (sizeof t') in *)
(*   let b' = { content = content_bytes b; start = size *^ i +^ b.start; length = size *^ j  } in *)
(*   assume (to_seq #t' #ty b' == Seq.slice (to_seq b) (v i) (v i + v j)); *)
(*   b' *)

assume val offset: #t':sizeof_t -> #ty:serializable t' -> 
  b:buffer ty -> i:t{v i <= length b} -> 
  Tot (b':buffer ty{
    start b' = start b + (sizeof t' * v i)
    /\ length b' = length b - v i
    /\ to_seq b' == Seq.slice (to_seq b) (v i) (length b)})

noeq type buffer_tuple (#a:sizeof_t) (#b:sizeof_t) (s1:serializable a) (s2:serializable b) =  {
    fst: buffer s1;
    snd: buffer s2
  }

(* There should be a "sizeof" calculus to compute that automatically on record types *)
assume BufferTupleHasSize: forall (a:sizeof_t) (b:sizeof_t) (s1:serializable t') (s2:serializable t').
  hasSize (buffer_tuple s1 s2) /\ sizeof (buffer_tuple s1 s2) = sizeof (buffer s1) + sizeof (buffer s2)

val split: #t':sizeof_t -> #ty:serializable t' ->
  b:buffer ty -> i:t{v i <= length b} -> 
  Tot (tu:buffer_tuple ty ty{Seq.length (to_seq tu.fst) = v i
    /\ to_seq tu.fst @| to_seq tu.snd == to_seq b})
let split #t' #ty b i = 
  let fst = sub #t' #ty b 0ul i in
  let snd = offset #t' #ty  b i in
  Seq.lemma_eq_intro (to_seq fst @| to_seq snd) (to_seq b);
  {fst = fst ; snd = snd}

(* Cast a "buffer type" to its unrefined "bytes" type *)
let cast_to_bytes (#t:sizeof_t) (#ty:serializable t) (b:buffer ty)
  : Tot bytes
  = b

(* Cast an appropriate "bytes" object to the corresponding "buffer " type *)
let cast_to_buffer (#t:sizeof_t) (ty:serializable t) (b:bytes{length_bytes b % sizeof t = 0
  /\ Correct? (of_seq_bytes #t #ty (to_seq_byte b))})
  : Tot (buffer ty)
  = b

(* Generic cast function to cast pointers of one type into pointers of another type *)
(* Mostly for casts between native low level types (machine ints and pointers*)
let cast (#t:sizeof_t) (ty:serializable t) (#t':sizeof_t) (#ty':serializable t') 
  (b:buffer ty'{length_bytes (cast_to_bytes b) % sizeof t = 0
   /\ Correct? (of_seq_bytes #t #ty (to_seq_byte b))})
  : Tot (b':buffer ty) = cast_to_buffer #t ty (cast_to_bytes b)


(** **************************************************************** **)
(**           Concrete parser and serializers for basetypes          **)
(** **************************************************************** **)

#set-options "--lax"

assume val le_uint8_serializer: serializer byte
(* let le_uint8_serializer = *)
(*   let f:b:byte -> Tot (s:seq byte{Seq.length s = sizeof byte}) =  *)
(*     (fun s -> Seq.create 1 s) in *)
(*   assume(injective f); // TODO *)
(*   f *)

assume val le_uint8_parser: p:parser le_uint8_serializer{inverse le_uint8_serializer p}
(* let le_uint8_parser = *)
(*   let f: s:seq byte -> Tot (result byte) = *)
(*     fun s -> if Seq.length s = 1 then Correct (index s 0) *)
(* 		       else Error "Too long or too short" in *)
(*   assume (inverse le_uint8_serializer f); // TODO *)
(*   f *)

assume val le_uint16_serializer: serializer UInt16.t
(* let le_uint16_serializer = *)
(*   let f:b:UInt16.t -> Tot (s:seq byte{Seq.length s = sizeof UInt16.t}) = *)
(*     fun s -> *)
(*       let open FStar.UInt16 in *)
(*       let s0 = uint16_to_uint8 s in *)
(*       let s1 = uint16_to_uint8 (s >>^ 8ul)  in *)
(*       (Seq.create 1 s0) @| (Seq.create 1 s1) in *)
(*    assume (injective f); *)
(*    f *)

assume val le_uint16_parser : p:(parser #UInt16.t (le_uint16_serializer)){inverse le_uint16_serializer p}
(* let le_uint16_parser = *)
(*   let f : parser le_uint16_serializer = fun (s:seq byte) -> *)
(*     if Seq.length s = 2 then Correct ( *)
(*       let open FStar.UInt16 in *)
(*       uint8_to_uint16 (Seq.index s 0) +^ (uint8_to_uint16 (Seq.index s 1)) <<^  8ul *)
(*     ) *)
(*     else Error "Too short" in *)
(*   assume (inverse le_uint16_serializer f); *)
(*   f *)

assume val le_uint32_serializer: serializer UInt32.t
(* let le_uint32_serializer = *)
(*   let f:b:UInt32.t -> Tot (s:seq byte{Seq.length s = sizeof UInt32.t}) = *)
(*     fun s -> *)
(*       let open FStar.UInt32 in *)
(*       let s0 = uint32_to_uint8 s in *)
(*       let s1 = uint32_to_uint8 (s >>^ 8ul)  in *)
(*       let s2 = uint32_to_uint8 (s >>^ 16ul)  in *)
(*       let s3 = uint32_to_uint8 (s >>^ 24ul)  in *)
(*       (Seq.create 1 s0) @| (Seq.create 1 s1) @| (Seq.create 1 s2) @| (Seq.create 1 s3) in *)
(*    assume (injective f); *)
(*    f *)

assume val le_uint32_parser : p:(parser #UInt32.t (le_uint32_serializer)){inverse le_uint32_serializer p}
(* let le_uint32_parser = *)
(*   let f : parser le_uint32_serializer = fun (s:seq byte) -> *)
(*     if Seq.length s = 4 then Correct ( *)
(*       let open FStar.UInt32 in *)
(*       uint8_to_uint32 (Seq.index s 0) +^ ((uint8_to_uint32 (Seq.index s 1)) <<^  8ul) *)
(*       +^ ((uint8_to_uint32 (Seq.index s 2)) <<^  16ul) +^ ((uint8_to_uint32 (Seq.index s 3)) <<^  24ul)       *)
(*     ) *)
(*     else Error "Too short" in *)
(*   assume (inverse le_uint32_serializer f); *)
(*   f *)

assume val le_uint64_serializer: serializer UInt64.t
(* let le_uint64_serializer = *)
(*   let f:b:UInt64.t -> Tot (s:seq byte{Seq.length s = sizeof UInt64.t}) = *)
(*     fun s -> *)
(*       let open FStar.UInt64 in *)
(*       let s0 = uint64_to_uint8 s in *)
(*       let s1 = uint64_to_uint8 (s >>^ 8ul)  in *)
(*       let s2 = uint64_to_uint8 (s >>^ 16ul)  in *)
(*       let s3 = uint64_to_uint8 (s >>^ 24ul)  in *)
(*       let s4 = uint64_to_uint8 (s >>^ 32ul)  in *)
(*       let s5 = uint64_to_uint8 (s >>^ 40ul)  in *)
(*       let s6 = uint64_to_uint8 (s >>^ 48ul)  in *)
(*       let s7 = uint64_to_uint8 (s >>^ 56ul)  in *)
(*       (Seq.create 1 s0) @| (Seq.create 1 s1) @| (Seq.create 1 s2) @| (Seq.create 1 s3) @|(Seq.create 1 s4) @| (Seq.create 1 s5) @| (Seq.create 1 s6) @| (Seq.create 1 s7) in *)
(*    assume (injective f); *)
(*    f *)

assume val le_uint64_parser : p:(parser #UInt64.t (le_uint64_serializer)){inverse le_uint64_serializer p}
(* let le_uint64_parser = *)
(*   let f : parser le_uint64_serializer = fun (s:seq byte) -> *)
(*     if Seq.length s = 8 then Correct ( *)
(*       let open FStar.UInt64 in *)
(*       uint8_to_uint64 (Seq.index s 0) +^ ((uint8_to_uint64 (Seq.index s 1)) <<^  8ul) *)
(*       +^ ((uint8_to_uint64 (Seq.index s 2)) <<^  16ul) +^ ((uint8_to_uint64 (Seq.index s 3)) <<^  24ul)       *)
(*       +^ ((uint8_to_uint64 (Seq.index s 4)) <<^  32ul) +^ ((uint8_to_uint64 (Seq.index s 3)) <<^  40ul)       *)
(*       +^ ((uint8_to_uint64 (Seq.index s 6)) <<^  48ul) +^ ((uint8_to_uint64 (Seq.index s 3)) <<^  56ul)       *)
(*     ) *)
(*     else Error "Too short" in *)
(*   assume (inverse le_uint64_serializer f); *)
(*   f *)

assume val ptr_serializer: serializer bytes
assume val ptr_parser: p:parser ptr_serializer{inverse ptr_serializer p}

#reset-options

let u8  : serializable byte     = Serializable le_uint8_serializer  le_uint8_parser
let u16 : serializable UInt16.t = Serializable le_uint16_serializer le_uint16_parser
let u32 : serializable UInt32.t = Serializable le_uint32_serializer le_uint32_parser
let u64 : serializable UInt64.t = Serializable le_uint64_serializer le_uint64_parser
let ptr = Serializable ptr_serializer ptr_parser

#reset-options "--initial_fuel 0 --max_fuel 0"

assume val lemma_bytes_to_buffer: b:bytes ->
  Lemma (length_bytes b % sizeof byte = 0 
	/\ Seq.length (to_seq_byte b) = length_bytes b
	/\ Correct? (of_seq_bytes #byte #u8 (to_seq_byte b)))

type lbytes = (| len:UInt32.t & b:buffer u8{length b >= v len} |)

(* The following assume should be derived from the type structure *)
assume HasSizeLBytes: hasSize lbytes /\ sizeof lbytes = sizeof UInt32.t + sizeof bytes

val mk_lbytes: b:bytes -> len:UInt32.t{v len <= v b.length} -> Tot lbytes
let mk_lbytes b len = 
  lemma_bytes_to_buffer b;
  (|len, cast_to_buffer u8 b|)

val lb_length: b:lbytes -> Tot UInt32.t
let lb_length b = dfst b
val lb_bytes: b:lbytes -> Tot (buffer u8)
let lb_bytes b = dsnd b

val lb_offset: b:lbytes -> i:UInt32.t{v i <= v (lb_length b)} -> Tot lbytes
let lb_offset b i =
  let new_len = lb_length b -^ i in
  let new_bytes = offset (lb_bytes b) i in
  lemma_bytes_to_buffer new_bytes;
  (|new_len, new_bytes|)

val lb_sub: b:lbytes -> i:UInt32.t -> j:UInt32.t{v i + v j <= v (lb_length b)} -> Tot lbytes
let lb_sub b i j =
  let new_len = j in
  let new_bytes = sub (lb_bytes b) i j in
  lemma_bytes_to_buffer new_bytes;
  (|new_len, new_bytes|)

val lemma_lb_offset: b:lbytes -> i:UInt32.t{v i <= v (lb_length b)} ->
  Lemma (requires (True))
	(ensures  (v (lb_length (lb_offset b i)) = v (lb_length b) - v i
	  /\ lb_bytes (lb_offset b i) == offset (lb_bytes b) i))
let lemma_lb_offset b i = ()

val lemma_lb_sub: b:lbytes -> i:UInt32.t -> j:UInt32.t{v i + v j <= v (lb_length b)} ->
  Lemma (requires (True))
	(ensures  (v (lb_length (lb_sub b i j)) = v j 
	  /\ lb_bytes (lb_sub b i j) == sub (lb_bytes b) i j))
let lemma_lb_sub b i j = ()
