module FStar.Bytes

open FStar.Seq

module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

type byte = U8.t
abstract type bytes : eqtype = seq byte
abstract type string = seq FStar.Char.char

assume val repr_bytes : nat -> GTot (n:nat{n>0})
assume val lemma_repr_bytes_values: n:nat ->
  Lemma (   ( n < 256 <==> repr_bytes n = 1 )
         /\ ( (n >= 256 /\ n < 65536) <==> repr_bytes n = 2 )
         /\ ( (n >= 65536 /\ n < 16777216) <==> repr_bytes n = 3 )
         /\ ( (n >= 16777216 /\ n < 4294967296) <==> repr_bytes n = 4 )
         /\ ( (n >= 4294967296 /\ n < 1099511627776) <==> repr_bytes n = 5 )
         /\ ( (n >= 1099511627776 /\ n < 281474976710656) <==> repr_bytes n = 6 )
         /\ ( (n >= 281474976710656 /\ n < 72057594037927936) <==> repr_bytes n = 7 )
         /\ ( (n >= 72057594037927936 /\ n < 18446744073709551616) <==> repr_bytes n = 8 ) )


let length (b:bytes) : Tot (n:nat) = Seq.length b
//private let length (b:bytes) : Tot (n:nat{n = Seq.length b}) = Seq.length b

val index: b:bytes -> i:nat{i < length b} -> Tot byte
let index b i = Seq.index b i

(*
abstract val createEmpty: #a:Type -> Tot (s:(seq a){length s=0})
let createEmpty #a = MkSeq []
*)

//val createEmpty: Tot (s:(bytes){length s=0})

val create: len:nat -> v:byte -> Tot (bytes)
let rec create len v =
  if len = 0 then Seq.createEmpty
  else cons v (create (len - 1) v)

val init: len:nat -> contents: (i:nat { i < len } -> Tot byte) -> Tot (bytes)
let rec init_aux (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> Tot byte))
  : Tot (bytes) (decreases (len - k)) =
  if k + 1 = len then cons (contents k) Seq.createEmpty
  else cons (contents k) (init_aux len (k+1) contents)
let rec init len contents = if len = 0 then Seq.createEmpty else init_aux len 0 contents

type lbytes (n:nat) = b:bytes{length b = n}

val empty_bytes : lbytes 0
let empty_bytes = Seq.createEmpty


#set-options "--max_fuel 1 --max_ifuel 1 --detail_errors"
val abyte: byte -> Tot (lbytes 1)
let abyte b = Seq.create 1 b

let abyte2 (b:byte*byte) : Tot (lbytes 2) =
  Seq.init 2 (fun i -> if i = 0 then fst b else snd b)

let get (b:bytes) (pos:nat{pos < length b}) : Tot byte = Seq.index b pos

val append: b1:bytes -> b2:bytes -> Tot (b:bytes{length b = length b1 + length b2})
let append (b1:bytes) (b2:bytes) = append b1 b2

val lemma_append_empty: b:bytes -> Lemma
  (ensures (append b empty_bytes = b))

let rec lemma_append_empty (b:bytes) =
  Seq.append_empty_r b

val sub: b:bytes -> s:nat{s < length b} -> e:nat{e < length b /\ s <= e} ->
  Tot (sub:bytes)
let sub b s e = Seq.slice b s e

let lemma_sub_length (b:bytes) (s:nat{s < length b})
  (e:nat{e < length b /\ s <= e})
  : Lemma (length (sub b s e) = e - s)
  = lemma_len_slice b s e

type uint_t (k:nat) = n:nat{n < pow2 FStar.Mul.(8 * k)}

#reset-options ""
(* Big endian integer value of a sequence of bytes *)
val decode_big_endian: b:bytes -> Tot (uint_t (length b)) (decreases (length b))
let rec decode_big_endian b =
  let open FStar.Mul in
  if length b = 0 then 0
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

//let rec eq_lemma b =
//  if length b = 0 then unit
//  else eq_lemma (tail b)




// TODO only use abstract functions on bytes rather than Seq functions

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

val slice: b:bytes -> i:nat -> j:nat{i <= j && j <= length b} ->
  Tot (bytes) (decreases (length b))
let rec slice b i j =
  if i > 0 then slice (tail b) (i - 1) (j - 1)
  else
    if j = 0 then Seq.createEmpty
    else cons (head b) (slice (tail b) i (j - 1))

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




(* code transfered from Platform.Bytes.fst *)

val seq_of_bytes: b:bytes -> GTot (bytes)
let seq_of_bytes b = b

val op_At_Bar: bytes -> bytes -> Tot bytes
let op_At_Bar (b1:bytes) (b2:bytes) = append b1 b2

(*@ type (l:nat) lbytes = (b:bytes){Length (b) = l} @*)
(*type lbytes (l:nat) = b:bytes{length b = l}*)


val createBytes : l:nat -> byte -> Tot (lbytes l)
let createBytes l b = Seq.create l b

val initBytes: l:nat -> (i:nat {i<l} -> Tot byte) -> Tot (lbytes l)
let initBytes l f = Seq.init l f

assume val bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} -> Tot (lbytes l)

assume val int_of_bytes : b:bytes -> Tot (n:nat)

assume val int_of_bytes_of_int : l:nat -> n:nat{repr_bytes n <= l} ->
    Lemma (n = int_of_bytes (bytes_of_int l n))

assume val make: len:nat -> f:(n:nat{n < len} -> Tot byte) -> Tot (lbytes len)
assume val utf8_encode: string -> bytes
assume val utf8_decode: bytes -> option string


(*@ assume val equalBytes : (b0:bytes -> (b1:bytes -> (r:bool){r = True /\ B (b0) = B (b1) \/ r = False /\ B (b0) <> B (b1)})) @*)
assume val equalBytes : b1:bytes -> b2:bytes -> Tot (b:bool{b = (b1=b2)})
(*@ assume val xor : (bytes -> (bytes -> (nb:nat -> (b3:bytes){Length (b3) = nb}))) @*)

assume val xor: l:nat -> lbytes l -> lbytes l -> Tot (lbytes l)


private val split: b:bytes -> n:nat{n <= length b} ->
  Tot (x:(bytes * bytes) {length (fst (x))= n /\ length (snd (x)) == (length b) - n }) //(lbytes n * lbytes (length b - n))
//val split: bytes -> nat -> Tot (bytes * bytes)
let split b (n:nat { n <= length b}) = split b n
(*
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
*)

(*
val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes -> t2:bytes {length s1 = length t1 \/ length s2 = length t2} ->
  Lemma (requires (Seq.equal (append s1 s2) (append t1 t2)))
        (ensures (Seq.equal s1 t1 /\ Seq.equal s2 t2))
*)


(*
let length (b:bytes) : Tot (n:nat) = Seq.length b
//private let length (b:bytes) : Tot (n:nat{n = Seq.length b}) = Seq.length b

val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes ->
  t2:bytes {length s1 = length t1 \/ length s2 = length t2} ->
  Lemma (requires (Seq.equal (append s1 s2) (append t1 t2)))
        (ensures (Seq.equal s1 t1 /\ Seq.equal s2 t2))
*)
(*
val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes ->
  t2:bytes ->
  Lemma (requires (Seq.equal (append s1 s2) (append t1 t2)))
        (ensures (Seq.equal s1 t1 /\ Seq.equal s2 t2))

let lemma_append_inj s1 s2 t1 t2 = admit()
*)

val lemma_append_inj: s1:bytes -> s2:bytes -> t1:bytes ->
  t2:bytes {length s1 = length t1 \/ length s2 = length t2} ->
  Lemma (requires (equal (append s1 s2) (append t1 t2)))
        (ensures (equal s1 t1 /\ equal s2 t2))
let lemma_append_inj s1 s2 t1 t2 = admit() (* CH: this used to fail *)


let append_empty_bytes_l (l: bytes): Lemma (ensures (empty_bytes @| l == l)) =
  Seq.append_empty_l l

let append_empty_bytes_r (l: bytes): Lemma (ensures (l @| empty_bytes == l)) =
  Seq.append_empty_r l

let append_assoc (l1 l2 l3: bytes): Lemma
  (ensures ((l1 @| l2) @| l3 == l1 @| (l2 @| l3))) =
  Seq.append_assoc l1 l2 l3


val lemma_append_assoc: b1:bytes -> b2:bytes -> b3:bytes ->
  Lemma (append b1 (append b2 b3) == append (append b1 b2) b3)

let lemma_append_assoc b1 b2 b3 = admit()


(*

val append_assoc : #a:Type -> l1:list a -> l2:list a -> l3: list a ->
  Lemma (append l1 (append l2 l3) == append (append l1 l2) l3)
let rec append_assoc #a l1 l2 l3 =
  match l1 with
  | [] -> ()
  | h1 :: t1 -> append_assoc t1 l2 l3

*)


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
