(*
   Copyright 2008-2017 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.Bytes
module S = FStar.Seq
module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Str = FStar.String
module Chr = FStar.Char
module IC = FStar.Int.Cast

let bytes = s: S.seq byte {S.length s < pow2 32}
let len (b: bytes) = U32.uint_to_t (S.length b)

let reveal b = b
let length_reveal x = ()

let hide s = s

let hide_reveal x = ()
let reveal_hide x = ()

let empty_bytes = S.Seq.empty
let empty_unique b = S.lemma_empty b

let get b i = Seq.index b (U32.v i)

(* TODO: fix me JROESCH 10/5 *)
let set_byte bs pos b = bs

let extensionality b1 b2 =
  assert (forall (b: bytes) (x: nat{x < U32.v (len b)}). {:pattern (Seq.index b x)}
        b.[ U32.uint_to_t x ] == Seq.index b x);
  S.lemma_eq_intro b1 b2

let create (len: u32) (v: byte) =
  S.lemma_create_len (U32.v len) v;
  S.create (U32.v len) v

let init len f =
  let f' (i: nat{i < U32.v len}) = f (U32.uint_to_t i) in
  S.lemma_init_len (U32.v len) f';
  S.init (U32.v len) f'

let append b1 b2 = Seq.append b1 b2
let slice b s e = Seq.slice b (U32.v s) (U32.v e)
let sub b s l = Seq.slice b (U32.v s) (U32.v s + U32.v l)

let split b k =
  let x, y = S.split b (U32.v k) in
  S.lemma_split b (U32.v k);
  x, y

(* TODO: Move this out of here *)
private
let lemma_div_pow2 (k: nat{k <= 32}) (x: nat) (y: nat{y < pow2 k})
  : Lemma ((op_Multiply (pow2 k) x + y) / (pow2 k) = x) =
  FStar.Math.Lemmas.division_addition_lemma y (pow2 k) x;
  assert ((op_Multiply (pow2 k) x + y) / (pow2 k) = y / (pow2 k) + x);
  FStar.Math.Lemmas.small_division_lemma_1 y (pow2 k)

#set-options "--z3rlimit_factor 4"
private
let lemma_mod_pow2 (k: nat{k <= 32}) (x: nat) (y: nat{y < pow2 k})
  : Lemma ((op_Multiply (pow2 k) x + y) % (pow2 k) = y) =
  assert (op_Multiply (pow2 k) x + y = y + op_Multiply x (pow2 k));
  FStar.Math.Lemmas.lemma_mod_plus y x (pow2 k);
  FStar.Math.Lemmas.small_modulo_lemma_1 y (pow2 k)

let rec repr_bytes n =
  if n < 256
  then 1
  else
    if n < 65536
    then 2
    else
      if n < 16777216
      then
        (assert_norm (pow2 24 == 16777216);
          3)
      else
        if n < 4294967296
        then 4
        else
          if n < 1099511627776
          then
            (assert_norm (pow2 40 == 1099511627776);
              5)
          else
            if n < 281474976710656
            then
              (assert_norm (pow2 48 == 281474976710656);
                6)
            else
              if n < 72057594037927936
              then
                (assert_norm (pow2 56 == 72057594037927936);
                  7)
              else
                if n < 18446744073709551616
                then 8
                else
                  let n' = n / pow2 8 in
                  let k' = repr_bytes n' in
                  FStar.Math.Lemmas.pow2_plus 8 (op_Multiply 8 k');
                  1 + k'

let lemma_repr_bytes_values n = ()

let repr_bytes_size = admit ()

// Interpret a sequence of bytes as a mathematical integer encoded in big endian
private
let rec int_of_bytes' (b: bytes) : Tot (uint_k (U32.v (len b))) (decreases (U32.v (len b))) =
  let open FStar.Mul in
  let open FStar.UInt32 in
  let k = U32.v (len b) in
  if k = 0
  then 0
  else
    let b1, b0 = split b (len b -^ 1ul) in
    let x = UInt8.v (get b0 0ul) in
    let y: uint_k (k - 1) = int_of_bytes' b1 in
    let z = pow2 8 * y + x in
    FStar.Math.Lemmas.pow2_plus 8 (op_Multiply 8 (k - 1));
    z
let int_of_bytes = int_of_bytes'

#reset-options "--initial_fuel 2 --initial_ifuel 2 --z3rlimit 30"
let rec bytes_of_int' (#k: nat{k <= 32}) (n: uint_k k)
  : Tot (b: lbytes k {int_of_bytes b = n}) (decreases k) = admit ()
(* let open FStar.Mul in
    match k with
    | 0 -> empty_bytes
    | 1 -> abyte (U8.uint_to_t n)
    | _ ->
      FStar.Math.Lemmas.pow2_le_compat (8*k) 16;
      FStar.Math.Lemmas.lemma_mod_lt n 256;
      FStar.Math.Lemmas.lemma_div_lt n (8*k) 8;
      let r0:nat = U.mod n 256 in
      let r:nat = U.div n (pow2 8) in
      assert(pow2 8 * r + r0 = n);
      let b0 = abyte (U8.uint_to_t r0) in
      let b = bytes_of_int' #(k - 1) r in
      let result = b @| b0 in
      assume( //TODO: FIXME ... move this to the lemma?
        let n' = int_of_bytes result in
        let b', b0' = split (b @| b0) (len b) in
        b' = b /\ b0' = b0 /\ U8.v (get b0' 0ul) = r0 /\
        int_of_bytes b' = r /\ n' = pow2 8 * r + r0 /\ n' = n);
      result *)
let bytes_of_int = bytes_of_int'

let int_of_bytes_of_int #k n = ()

#reset-options "--initial_fuel 2 --initial_ifuel 2 --max_ifuel 2 --max_fuel 2 --z3rlimit 60"
private
let rec lemma_bytes_of_int_of_bytes' (b: bytes{U32.v (len b) <= 32})
  : Lemma (requires True) (ensures bytes_of_int (int_of_bytes b) == b) (decreases (U32.v (len b))) =
  admit ()
(* let k = U32.v (len b) in
   let n = int_of_bytes b in
   let b' = bytes_of_int #k n in
   match k with
   | 0 -> ()
   | 1 -> extensionality b b'
   | _ ->
     let open FStar.Mul in
     assert_norm (pow2 8 = 256);
     FStar.Math.Lemmas.pow2_le_compat (8*k) 16;
     FStar.Math.Lemmas.lemma_mod_lt n 256;
     FStar.Math.Lemmas.lemma_div_lt n (8*k) 8;
     let r0 : n:nat{n < pow2 8} = U.mod n 256 in
     let r : n:nat{n < pow2 (8*(k-1))} = U.div n (pow2 8) in
     let r0' = abyte (U8.uint_to_t r0) in
     let r' = bytes_of_int #(k - 1) r in
     let r'', r0'' = split b U32.(len b -^ 1ul) in
     assert(r'' @| r0'' = b);
     let x = UInt8.v (r0''.[0ul]) in
     let y = int_of_bytes r'' in
     let z = pow2 8 * y + x in
     lemma_div_pow2 8 y x;
     assert(r = int_of_bytes r'');
     lemma_bytes_of_int_of_bytes' r'';
     lemma_mod_pow2 8 y x;
     assert(x = r0 /\ r0'.[0ul] = r0''.[0ul]);
     extensionality r0'' r0';
     assert(r' @| r0' = r'' @| r0'') *)

let bytes_of_int_of_bytes b = lemma_bytes_of_int_of_bytes' b

//TODO
let int32_of_bytes b = admit ()
let int16_of_bytes b = admit ()
let int8_of_bytes b = admit ()
let bytes_of_int32 b = admit ()
let bytes_of_int16 b = admit ()
let bytes_of_int8 b = admit ()

let rec xor' (n: u32) (b1: minbytes (U32.v n)) (b2: minbytes (U32.v n))
  : Tot (b : lbytes (U32.v n)) (decreases (U32.v n)) =
  if n = 0ul
  then empty_bytes
  else
    let u, v = split b1 1ul in
    let x, y = split b2 1ul in
    (abyte (U8.logxor (get u 0ul) (get x 0ul))) @| (xor' (U32.sub n 1ul) v y)

let xor = xor'
private
let rec lemma_xor_commutative (k: u32) (b1: minbytes (U32.v k)) (b2: minbytes (U32.v k))
  : Lemma (ensures xor k b1 b2 == xor k b2 b1) (decreases (U32.v k)) =
  if k = 0ul
  then ()
  else
    let u, v = split b1 1ul in
    let x, y = split b2 1ul in
    U.logxor_commutative (U8.v (u.[ 0ul ])) (U8.v (x.[ 0ul ]));
    lemma_xor_commutative U32.(k -^ 1ul) v y

let xor_commutative n b1 b2 = lemma_xor_commutative n b1 b2

let xor_append b1 b2 x1 x2 = admit ()
private
let lemma_xor_idempotent_1 (b1: lbytes 1) (b2: lbytes 1) : Lemma (xor 1ul (xor 1ul b1 b2) b2 = b1) =
  let b = xor 1ul b1 b2 in
  let b' = xor 1ul b b2 in
  let u0: U.uint_t 8 = U8.v (b1.[ 0ul ]) in
  let x0: U.uint_t 8 = U8.v (b2.[ 0ul ]) in
  assert (U8.v b.[ 0ul ] = U.logxor u0 x0);
  assert (U8.v b'.[ 0ul ] = U.logxor (U.logxor u0 x0) x0);
  U.logxor_inv u0 x0;
  extensionality b' b1

#reset-options "--z3rlimit 30 --initial_fuel 2 --initial_ifuel 2 --max_ifuel 2 --max_fuel 2"
let rec lemma_xor_idempotent (k: u32) (b1: lbytes (U32.v k)) (b2: lbytes (U32.v k))
  : Lemma (ensures xor k (xor k b1 b2) b2 = b1) (decreases (U32.v k)) =
  match U32.v k with
  | 0 -> ()
  | 1 -> lemma_xor_idempotent_1 b1 b2
  | _ ->
    let u, v = split b1 1ul in
    let x, y = split b2 1ul in
    lemma_xor_idempotent_1 u x;
    xor_append u v x y;
    xor_append (xor 1ul u x) (xor U32.(k -^ 1ul) v y) x y;
    lemma_xor_idempotent U32.(k -^ 1ul) v y

let xor_idempotent n b1 b2 = lemma_xor_idempotent n b1 b2

#reset-options "--z3rlimit 30 --initial_ifuel 2 --initial_fuel 2 --max_ifuel 2 --max_fuel 2"
let utf8_encode s =
  let len: n: nat{n < pow2 30} = Str.length s in
  let rec aux (i: nat{i < len}) (acc: bytes{U32.v (len acc) <= op_Multiply 4 i})
    : Tot (b: bytes{U32.v (len b) <= op_Multiply 4 len}) (decreases (len - i)) =
    if i = len - 1
    then acc
    else
      let cur = Str.index s i in
      if let open U32 in cur <^ 128ul
      then
        let c = abyte (IC.uint32_to_uint8 cur) in
        aux (i + 1) (acc @| c)
      else
        if let open U32 in cur <^ 2048ul
        then
          let c0 = abyte (IC.uint32_to_uint8 U32.(128ul +^ rem cur 128ul)) in
          let c1 = abyte (IC.uint32_to_uint8 U32.(192ul +^ shift_right cur 6ul)) in
          aux (i + 1) (acc @| c1 @| c0)
        else
          if let open U32 in cur <^ 65536ul
          then
            let c0 = abyte (IC.uint32_to_uint8 U32.(128ul +^ rem cur 128ul)) in
            let c1 = U32.rem (U32.shift_right cur 6ul) 128ul in
            let c1 = abyte (IC.uint32_to_uint8 U32.(128ul +^ c1)) in
            let c2 = U32.rem (U32.shift_right cur 12ul) 16ul in
            let c2 = abyte (IC.uint32_to_uint8 U32.(224ul +^ c2)) in
            aux (i + 1) (acc @| c2 @| c1 @| c0)
          else
            let c0 = abyte (IC.uint32_to_uint8 U32.(128ul +^ rem cur 128ul)) in
            let c1 = U32.rem (U32.shift_right cur 6ul) 128ul in
            let c1 = abyte (IC.uint32_to_uint8 U32.(128ul +^ c1)) in
            let c2 = U32.rem (U32.shift_right cur 12ul) 128ul in
            let c2 = abyte (IC.uint32_to_uint8 U32.(128ul +^ c2)) in
            let c3 = U32.rem (U32.shift_right cur 18ul) 8ul in
            let c3 = abyte (IC.uint32_to_uint8 U32.(480ul +^ c3)) in
            aux (i + 1) (acc @| c3 @| c2 @| c1 @| c0)
  in
  if len = 0 then empty_bytes else aux 0 empty_bytes

// assume val utf8_encode: (s:string{Str.length s < pow2 30}) -> b:bytes{lengthT b <= op_Multiply 4 (Str.length s) /\ b = utf8_encodeT s}

// (*)
// let utf8_decode (b:bytes) : option (s:string{Str.length s <= length b}) =
//   let rec
// *)
// (* Little endian integer value of a sequence of bytes *)
// (*)
// val decode_little_endian: b:bytes ->
//   Tot (uint_t (length b)) (decreases (length b))
// let rec decode_little_endian b =
//   let open FStar.Mul in
//   if length b = 0 then 0
//   else UInt8.v (head b) + pow2 8 * decode_little_endian (tail b)

// val decode_little_endian_acc: b:bytes -> k:nat -> acc:uint_t k ->
//     Tot (uint_t (k + length b)) (decreases (length b))

// let rec decode_little_endian_acc b k acc =
//   let open FStar.Mul in
//     if length b = 0 then acc
//     else
//       let acc2 = UInt8.v (head b) + 256 * acc in
//         FStar.Math.Lemmas.pow2_plus 8 (8 * k);
//         assert(UInt8.v (last b) + 256 * acc < pow2 (8 * (k+1)));
//         decode_little_endian_acc (tail b) (k + 1) acc2

// val eq_lemma_decode_little_endian: b:bytes ->
//   Lemma (decode_little_endian b = decode_little_endian_acc b 0 0)
// *)
// (*
// val eq_lemma_decode_big_endion:
//   b:bytes ->
//   Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)
//   (decreases (lengtjh ))

// let rec eq_lemma_decode_big_endion b =
//   if length b = 0 then ()
//   //else eq_lemma_decode_big_endion (tail b)
//   else
//     let sub = slice b 0 (length b - 1) in
//     assert(length sub = length b - 1);
//     eq_lemma_decode_big_endion sub
// *)
// (*
// val eq_lemma_decode_big_endion: b:bytes ->
//   GTot (u:unit{decode_big_endian b = decode_big_endian_acc b 0 0})
//   (decreases (length b))
// *)
// (*
// val eq_lemma_decode_big_endian: b:bytes ->
//   Lemma (decode_big_endian b = decode_big_endian_acc b 0 0)

// let rec eq_lemma_decode_big_endion b =
//   if length b = 0 then ()
//   else eq_lemma_decode_big_endion (tail b)
//   //else eq_lemma_decode_big_endion (slice b 0 (length b - 1))
// *)
// (*)
// val get_binary: n:nat -> Tot (bytes)
// let rec get_binary n =
//   match n with
//   | 0 -> Seq.empty
//   | _ -> Seq.append (get_binary (n / 2)) (of_list [U8.uint_to_t (n % 2)])
// *)
// (*
// //val format: n:nat{n>0 /\ n <=20} -> Tot (bytes)
// val format: n:nat -> Tot (bytes)
// let format n =
//   match n with
//   | 1  -> (of_list [U8.uint_to_t 000000]) | 2  -> (of_list [U8.uint_to_t 00000])
//   | 3  -> (of_list [U8.uint_to_t 0000])   | 4  -> (of_list [U8.uint_to_t 000])
//   | 5  -> (of_list [U8.uint_to_t 00])     | 6  -> (of_list [U8.uint_to_t 0])
//   | 7  -> Seq.empty                 | 8  -> (of_list [U8.uint_to_t 000])
//   | 9  -> (of_list [U8.uint_to_t 00])     | 10 -> (of_list [U8.uint_to_t 0])
//   | 11 -> Seq.empty                 | 12 -> (of_list [U8.uint_to_t 0000])
//   | 13 -> (of_list [U8.uint_to_t 000])    | 14 -> (of_list [U8.uint_to_t 00])
//   | 15 -> (of_list [U8.uint_to_t 0])      | 16 -> Seq.empty
//   | 17 -> (of_list [U8.uint_to_t 000])    | 18 -> (of_list [U8.uint_to_t 00])
//   | 19 -> (of_list [U8.uint_to_t 0])      | 20 -> Seq.empty
//   | _ -> Seq.empty

// val binary_code_point: n:nat -> Tot (bytes)
// let binary_code_point n =
//   let b = (get_binary n) in
//     Seq.append (format(length b)) b

// val encode_utf8: n:nat -> Tot (bytes)
// let encode_utf8 n =
//   let code_point = (binary_code_point n) in
//     if n < 127 then Seq.append (of_list [U8.uint_to_t 0]) (code_point)
//     else if n < 2047 then
//       (of_list [U8.uint_to_t 110])
//     else Seq.empty
// *)
// (*
// #reset-options "--initial_fuel 1 --max_fuel 1"

// // turns an integer into a bytestream, little-endian
// val encode_little_endian: k:nat -> n:uint_t k ->
//  Tot (b:lbytes k {n == decode_little_endian b}) (decreases k)
// let rec little_bytes len n =
//  if len = 0ul then
//    Seq.empty
//  else
//    let len = len -^ 1ul in
//    let byte = UInt8.uint_to_t (n % 256) in
//    let n' = n / 256 in
// //   Math.Lemmas.pow2_plus 8 (8 * v len);
//    assert(n' < pow2 (8 * v len ));
//    let b' = little_bytes len n' in
//    let b = cons byte b' in
//    assert(Seq.equal b' (tail b));
//    b

// #reset-options "--initial_fuel 1 --max_fuel 1"
// val little_endian_null: len:nat{len < 16} -> Lemma
//  (little_endian (Seq.create len 0uy) == 0)

// val little_endian_singleton: n:UInt8.t -> Lemma
//  (little_endian (Seq.create 1 n) == UInt8.v n)

// #reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

// val little_endian_append: w1:bytes -> w2:bytes -> Lemma
//  (requires True)
//  (ensures
//    little_endian (Seq.append w1 w2) ==
//    little_endian w1 + pow2 (8 * Seq.length w1) * little_endian w2)
//  (decreases (Seq.length w1))
// *)

let iutf8_opt m = admit ()
// No definition for these: they're only meant for backwards compatibility with Platform.Bytes
let bytes_of_hex: string -> Tot bytes = admit ()
let hex_of_bytes: bytes -> Tot string = admit ()
let string_of_hex: string -> Tot string = admit ()
let hex_of_string: string -> Tot string = admit ()
let print_bytes: bytes -> Tot string = admit ()
let bytes_of_string: string -> bytes = admit () //abytes

