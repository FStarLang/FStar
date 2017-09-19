module FStar.Bytes

module S = FStar.Seq
module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Str = FStar.String
module Chr = FStar.Char

type byte = U8.t
abstract type bytes = S.seq byte

let reveal (b:bytes) : GTot (S.seq byte) = b
let hide (s:S.seq byte) : GTot (b:bytes{reveal b = s}) = s

let length (b:bytes) : Tot (n:nat{n = S.length (reveal b)}) = S.length b
type lbytes (l:nat) = b:bytes{length b = l}
let empty_bytes : lbytes 0 = S.createEmpty
let lemma_empty (b:bytes) : Lemma (length b = 0 ==> b = empty_bytes) = S.lemma_empty b

let get (b:bytes) (pos:nat{pos < length b}) : Tot byte = Seq.index b pos
unfold let op_String_Access (b:bytes) (i:nat{i < length b}) = get b i

type bytes8 = b:bytes{length b < pow2 8}
let length8 (b:bytes8) : U8.t = U8.uint_to_t (length b)
type lbytes8 (l:U8.t) = b:bytes8{length8 b = l}
let get8 (b:bytes8) (i:U8.t{U8.(i <^ length8 b)}) = b.[U8.v i]

type bytes16 = b:bytes{length b < pow2 16}
let length16 (b:bytes16) : U16.t = U16.uint_to_t (length b)
type lbytes16 (l:U16.t) = b:bytes16{length16 b = l}
let get16 (b:bytes16) (i:U16.t{U16.(i <^ length16 b)}) = b.[U16.v i]

type bytes32 = b:bytes{length b < pow2 32}
let length32 (b:bytes32) : U32.t = U32.uint_to_t (length b)
type lbytes32 (l:U32.t) = b:bytes32{length32 b = l}
let get32 (b:bytes32) (i:U32.t{U32.(i <^ length32 b)}) = b.[U32.v i]

let create (len:nat) (v:byte) : b:lbytes len{forall (i:nat{i<len}). b.[i] = v} =
  S.lemma_create_len len v;
  S.create len v

let create8 (len:U8.t) (v:byte) : b:lbytes8 len{forall (i:U8.t{U8.(i <^ len)}). get8 b i = v} =
  create (U8.v len) v
let create16 (len:U16.t) (v:byte) : b:lbytes16 len{forall (i:U16.t{U16.(i <^ len)}). get16 b i = v} =
  create (U16.v len) v
let create32 (len:U32.t) (v:byte) : b:lbytes32 len{forall (i:U32.t{U32.(i <^ len)}). get32 b i = v} =
  create (U32.v len) v

let init (len:nat) (f: i:nat{i<len} -> byte) : b:lbytes len{forall (i:nat{i<len}). get b i = f i} =
  S.lemma_init_len len f;
  S.init len f

let init8 (len:U8.t) (f: i:U8.t{U8.(i <^ len)} -> byte)
  : b:lbytes8 len{forall (i:U8.t{U8.(i <^ len)}). get8 b i = f i} =
  init (U8.v len) (fun (i:nat{i < U8.v len}) -> f (U8.uint_to_t i))
let init16 (len:U16.t) (f: i:U16.t{U16.(i <^ len)} -> byte)
  : b:lbytes16 len{forall (i:U16.t{U16.(i <^ len)}). get16 b i = f i} =
  init (U16.v len) (fun (i:nat{i < U16.v len}) -> f (U16.uint_to_t i))
let init32 (len:U32.t) (f: i:U32.t{U32.(i <^ len)} -> byte)
  : b:lbytes32 len{forall (i:U32.t{U32.(i <^ len)}). get32 b i = f i} =
  init (U32.v len) (fun (i:nat{i < U32.v len}) -> f (U32.uint_to_t i))

let abyte (b:byte) : lbytes 1 = create 1 b
let twobytes (b:byte*byte) : Tot (lbytes 2) =
  Seq.init 2 (fun i -> if i = 0 then fst b else snd b)

let abyte8 (b:byte) : lbytes8 1uy = abyte b
let abyte16 (b:byte) : lbytes16 1us = abyte b
let abyte32 (b:byte) : lbytes32 1ul = abyte b

let twobytes8 (b:byte*byte) : lbytes8 2uy = twobytes b
let twobytes16 (b:byte*byte) : lbytes16 2us = twobytes b
let twobytes32 (b:byte*byte) : lbytes32 2ul = twobytes b

let append (b1:bytes) (b2:bytes) : b:bytes{length b = length b1 + length b2} =
  Seq.append b1 b2
val lemma_append_empty: b:bytes -> Lemma (ensures (append b empty_bytes = b /\ append empty_bytes b = b))
let op_Hat (b1:bytes) (b2:bytes) : b:bytes{length b = length b1 + length b2} = append b1 b2
let op_At_Bar (b1:bytes) (b2:bytes) : b:bytes{length b = length b1 + length b2} = append b1 b2

let slice (b:bytes) (s:nat{s < length b}) (e:nat{e < length b /\ s <= e}) : b:bytes{length b = e - s} =
  Seq.slice b s e
type range = a:nat & b:nat{a <= b}
let op_Amp_Colon (a:nat) (b:nat{a <= b}) : range = (| a, b |)
let op_Array_Access (b:bytes) ((|x, y|):r:range{dsnd r < length b}) = slice b x y
let op_At (b:bytes) ((|x,y|):range{y < length b}) = slice b x y

let sub (b:bytes) (s:nat{s < length b}) (l:nat{s + l < length b}) : b:bytes{length b = l} =
  b @ (s &: (s+l))

(* Big endian integer value of a sequence of bytes *)
val decode_big_endian: b:bytes -> Tot (U.uint_t (length b)) (decreases (length b))
let rec decode_big_endian b =
  let open FStar.Mul in
  if b = empty_bytes then 0
  else UInt8.v (last b) + pow2 8 * decode_big_endian (Seq.slice b 0 (length b - 1))

val decode_big_endian_acc: b:bytes -> k:nat -> acc:uint_t k ->
  Tot (uint_t (k + length b)) (decreases (length b))

let rec decode_big_endian_acc b k acc =
  let open FStar.Mul in
    if length b = 0 then acc
    else
      let acc2 = UInt8.v (last b) + 256 * acc in
      FStar.Math.Lemmas.pow2_plus 8 (8 * k);
      //assert(255 + 256 * acc < pow2 (8 * (k + 1)));
      assert(UInt8.v (last b) + 256 * acc < pow2 (8 * (k+1)));
      //assert(acc2 < pow2 8 + pow2 (8 * (k+1)));
      decode_big_endian_acc (slice b 0 (length b - 1)) (k + 1) acc2

val eq_lemma_decode_big_endion: b:bytes ->
  Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)

(* Little endian integer value of a sequence of bytes *)
val decode_little_endian: b:bytes ->
  Tot (uint_t (length b)) (decreases (length b))
let rec decode_little_endian b =
  let open FStar.Mul in
  if length b = 0 then 0
  else UInt8.v (head b) + pow2 8 * decode_little_endian (tail b)

val decode_little_endian_acc: b:bytes -> k:nat -> acc:uint_t k ->
    Tot (uint_t (k + length b)) (decreases (length b))

let rec decode_little_endian_acc b k acc =
  let open FStar.Mul in
    if length b = 0 then acc
    else
      let acc2 = UInt8.v (head b) + 256 * acc in
        FStar.Math.Lemmas.pow2_plus 8 (8 * k);
        assert(UInt8.v (last b) + 256 * acc < pow2 (8 * (k+1)));
        decode_little_endian_acc (tail b) (k + 1) acc2

val eq_lemma_decode_little_endian: b:bytes ->
  Lemma (decode_little_endian b = decode_little_endian_acc b 0 0)

(*
val eq_lemma_decode_big_endion:
  b:bytes ->
  Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)
  (decreases (lengtjh ))

let rec eq_lemma_decode_big_endion b =
  if length b = 0 then ()
  //else eq_lemma_decode_big_endion (tail b)
  else
    let sub = slice b 0 (length b - 1) in
    assert(length sub = length b - 1);
    eq_lemma_decode_big_endion sub
*)
(*
val eq_lemma_decode_big_endion: b:bytes ->
  GTot (u:unit{decode_big_endian b = decode_big_endian_acc b 0 0})
  (decreases (length b))
*)
(*
val eq_lemma_decode_big_endian: b:bytes ->
  Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)

let rec eq_lemma_decode_big_endion b =
  if length b = 0 then ()
  else eq_lemma_decode_big_endion (tail b)
  //else eq_lemma_decode_big_endion (slice b 0 (length b - 1))
*)

assume val make: len:nat -> f:(n:nat{n < len} -> Tot byte) -> Tot (lbytes len)
assume val utf8_encode: string -> bytes
assume val utf8_decode: bytes -> option string

assume val xor: l:nat -> lbytes l -> lbytes l -> Tot (lbytes l)

val split: b:bytes -> n:nat{n <= length b} ->
  Tot (x:(bytes * bytes) {length (fst (x)) = n
    /\ length (snd (x)) == (length b) - n }) //(lbytes n * lbytes (length b - n))

let split b (n:nat { n <= length b}) = Seq.split b n

val lemma_split : s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Lemma
  (ensures ((fst (split s i)) @| (snd (split s i)) = s))
let lemma_split s i =
  cut (Seq.equal ((fst (split s i)) @| (snd (split s i)))  s)

val split_eq: s:bytes -> i:nat{(0 <= i /\ i <= length s)} -> Pure
  (x:(bytes * bytes){length (fst x) = i && length (snd x) = length s - i})
  (requires True)
  (ensures (fun x -> ((fst x) @| (snd x) = s)))
let split_eq s i =
  let x = split s i in
  lemma_split s i;
  x

val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes -> t2:bytes {length s1 = length t1 \/ length s2 = length t2} ->
  Lemma (requires (Seq.equal (append s1 s2) (append t1 t2)))
        (ensures (Seq.equal s1 t1 /\ Seq.equal s2 t2))
let lemma_append_inj s1 s2 t1 t2 = admit()

let append_empty_bytes_l (l: bytes): Lemma (ensures (empty_bytes @| l == l)) =
  Seq.append_empty_l l

let append_empty_bytes_r (l: bytes): Lemma (ensures (l @| empty_bytes == l)) =
  Seq.append_empty_r l

let append_assoc (l1 l2 l3: bytes): Lemma
  (ensures ((l1 @| l2) @| l3 == l1 @| (l2 @| l3))) =
  Seq.append_assoc l1 l2 l3


val get_binary: n:nat -> Tot (bytes)
let rec get_binary n =
  match n with
  | 0 -> Seq.createEmpty
  | _ -> Seq.append (get_binary (n / 2)) (of_list [U8.uint_to_t (n % 2)])

(*
//val format: n:nat{n>0 /\ n <=20} -> Tot (bytes)
val format: n:nat -> Tot (bytes)
let format n =
  match n with
  | 1  -> (of_list [U8.uint_to_t 000000]) | 2  -> (of_list [U8.uint_to_t 00000])
  | 3  -> (of_list [U8.uint_to_t 0000])   | 4  -> (of_list [U8.uint_to_t 000])
  | 5  -> (of_list [U8.uint_to_t 00])     | 6  -> (of_list [U8.uint_to_t 0])
  | 7  -> Seq.createEmpty                 | 8  -> (of_list [U8.uint_to_t 000])
  | 9  -> (of_list [U8.uint_to_t 00])     | 10 -> (of_list [U8.uint_to_t 0])
  | 11 -> Seq.createEmpty                 | 12 -> (of_list [U8.uint_to_t 0000])
  | 13 -> (of_list [U8.uint_to_t 000])    | 14 -> (of_list [U8.uint_to_t 00])
  | 15 -> (of_list [U8.uint_to_t 0])      | 16 -> Seq.createEmpty
  | 17 -> (of_list [U8.uint_to_t 000])    | 18 -> (of_list [U8.uint_to_t 00])
  | 19 -> (of_list [U8.uint_to_t 0])      | 20 -> Seq.createEmpty
  | _ -> Seq.createEmpty

val binary_code_point: n:nat -> Tot (bytes)
let binary_code_point n =
  let b = (get_binary n) in
    Seq.append (format(length b)) b

val encode_utf8: n:nat -> Tot (bytes)
let encode_utf8 n =
  let code_point = (binary_code_point n) in
    if n < 127 then Seq.append (of_list [U8.uint_to_t 0]) (code_point)
    else if n < 2047 then
      (of_list [U8.uint_to_t 110])
    else Seq.createEmpty
*)
(*
#reset-options "--initial_fuel 1 --max_fuel 1"

val encode_big_endian: k:nat -> n:uint_t k ->
  Tot (b:lbytes k {n = decode_big_endian b}) (decreases k)

// TODO

// turns an integer into a bytestream, little-endian
val encode_little_endian: k:nat -> n:uint_t k ->
 Tot (b:lbytes k {n == decode_little_endian b}) (decreases k)
let rec little_bytes len n =
 if len = 0ul then
   Seq.createEmpty
 else
   let len = len -^ 1ul in
   let byte = UInt8.uint_to_t (n % 256) in
   let n' = n / 256 in
//   Math.Lemmas.pow2_plus 8 (8 * v len);
   assert(n' < pow2 (8 * v len ));
   let b' = little_bytes len n' in
   let b = cons byte b' in
   assert(Seq.equal b' (tail b));
   b

#reset-options "--initial_fuel 1 --max_fuel 1"
val little_endian_null: len:nat{len < 16} -> Lemma
 (little_endian (Seq.create len 0uy) == 0)

val little_endian_singleton: n:UInt8.t -> Lemma
 (little_endian (Seq.create 1 n) == UInt8.v n)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

val little_endian_append: w1:bytes -> w2:bytes -> Lemma
 (requires True)
 (ensures
   little_endian (Seq.append w1 w2) ==
   little_endian w1 + pow2 (8 * Seq.length w1) * little_endian w2)
 (decreases (Seq.length w1))
*)
