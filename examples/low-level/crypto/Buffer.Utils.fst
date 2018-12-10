(*
   Copyright 2008-2018 Microsoft Research

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
module Buffer.Utils

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Int.Cast
open FStar.UInt8
open FStar.UInt32
open FStar.Buffer

open FStar.Math.Lemmas

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

let u32 = FStar.UInt32.t
let u8 = FStar.UInt8.t
let uint32s = buffer u32
let bytes = buffer u8

// JP: 20180402 this file dropped off CI a long while ago. Retained here,
// currently used as a testcase for KreMLin extraction, but I would love to see
// this re-enabled as a sanity check for F*'s long CI.
#set-options "--lax"

(** Rotate operators on UInt32.t *)
let op_Greater_Greater_Greater (a:u32) (s:u32{v s <= 32}) =
  let (m:u32{v m = 32}) = 32ul in
  (op_Greater_Greater_Hat a s) |^ (a <<^ (m -^ s))
let op_Less_Less_Less (a:u32) (s:u32{v s <= 32}) =
  let (m:u32{v m = 32}) = 32ul in
  (op_Less_Less_Hat a s) |^ (op_Greater_Greater_Hat a (m -^ s))

(** Inplace xor operation on bytes *)
(* TODO: add functional spec *)
val xor_bytes_inplace: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_bytes_inplace output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = len -^ 1ul in
      let in1i = index in1 i in
      let oi   = index output i in
      let oi   = UInt8.logxor in1i oi in
      output.(i) <- oi;
      xor_bytes_inplace output in1 i
    end

val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

#reset-options "--initial_fuel 0 --max_fuel 0"

let lemma_uint32_of_bytes (a:t) (b:t) (c:t) (d:t) : Lemma
  (requires (v a < pow2 8 /\ v b < pow2 8 /\ v c < pow2 8 /\ v d < pow2 8))
  (ensures  (v a + pow2 8 * v b < pow2 16
    /\ v a + pow2 8 * v b + pow2 16 * v c < pow2 24
    /\ v a + pow2 8 * v b + pow2 16 * v c + pow2 24 * v d < pow2 32))
  = pow2_plus 8 8;
    lemma_euclidean_division (v a) (v b) (pow2 8);
    pow2_plus 8 16;
    lemma_euclidean_division (v a + pow2 8 * v b) (v c) (pow2 16);
    pow2_plus 8 24;
    lemma_euclidean_division (v a + pow2 8 * v b + pow2 16 * v c) (v d) (pow2 24)

(** Reads an unsigned int32 out of 4 bytes *)
val uint32_of_bytes: b:bytes{length b >= 4} -> STL u32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 b
    /\ v r = U8.(v (get h0 b 0)
		 + pow2 8 * v (get h0 b 1)
		 + pow2 16 * v (get h0 b 2)
		 + pow2 24 * v (get h0 b 3)) ))
let uint32_of_bytes (b:bytes{length b >= 4}) =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b0' = uint8_to_uint32 b0 in
  let b1' = uint8_to_uint32 b1 in
  let b2' = uint8_to_uint32 b2 in
  let b3' = uint8_to_uint32 b3 in
  pow2_lt_compat 32 8;
  cut (v b0' = U8.v b0 /\ v b1' = U8.v b1 /\ v b2' = U8.v b2 /\ v b3' = U8.v b3);
  pow2_lt_compat 16 8;
  pow2_lt_compat 24 16;
  pow2_lt_compat 32 24;
  pow2_plus 8 8;
  pow2_plus 8 16;
  pow2_plus 8 24;
  let b1'' = b1' <<^ 8ul in
  let b2'' = b2' <<^ 16ul in
  let b3'' = b3' <<^ 24ul in
  cut (v b1'' = pow2 8 * U8.v b1 /\ v b2'' = pow2 16 * U8.v b2 /\ v b3'' = pow2 24 * U8.v b3);
  lemma_uint32_of_bytes b0' b1' b2' b3';
  b0' +^ b1'' +^ b2'' +^ b3''

#reset-options "--z3rlimit 20"

(** Stores the content of a byte buffer into a unsigned int32 buffer *)
(* TODO: add functional spec *)
val bytes_of_uint32s: output:bytes -> m:uint32s{disjoint output m} -> len:u32{v len <=length output /\ v len<=op_Multiply 4 (length m)} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec bytes_of_uint32s output m l =
  if l >^ 0ul then
    begin
    let rem = l %^ 4ul in
    if UInt32.gt rem 0ul then
      begin
      let l = l -^ rem in
      let x = index m (l /^ 4ul) in
      let b0 = uint32_to_uint8 (x &^ 255ul) in
      output.(l) <- b0;
      if UInt32.gt rem 1ul then
        begin
        let b1 = uint32_to_uint8 ((x >>^ 8ul) &^ 255ul) in
        output.(l +^ 1ul) <- b1;
	if UInt32.gt rem 2ul then
	  begin
	  let b2 = uint32_to_uint8 ((x >>^ 16ul) &^ 255ul) in
	  output.(l +^ 2ul) <- b2
          end
	else ()
	end
      else ();
      bytes_of_uint32s output m l
      end
    else
      begin
      let l = l -^ 4ul in
      let x = index m (l /^ 4ul) in
      let b0 = uint32_to_uint8 (x &^ 255ul) in
      let b1 = uint32_to_uint8 ((x >>^ 8ul) &^ 255ul) in
      let b2 = uint32_to_uint8 ((x >>^ 16ul) &^ 255ul) in
      let b3 = uint32_to_uint8 ((x >>^ 24ul) &^ 255ul) in
      output.(l) <- b0;
      output.(l +^ 1ul) <- b1;
      output.(l +^ 2ul) <- b2;
      output.(l +^ 3ul) <- b3;
      bytes_of_uint32s output m l
      end
    end

(** Stores the content of a byte buffer into a unsigned int32 buffer *)
val bytes_of_uint32: output:bytes{length output >= 4} -> m:u32 -> STL unit
  (requires (fun h -> live h output))
  (ensures (fun h0 _ h1 -> live h1 output
    /\ modifies_1 output h0 h1
    /\ U8.v (get h1 output 0) = (U32.v m) % pow2 8
    /\ U8.v (get h1 output 1) = (U32.v m / pow2 8) % pow2 8
    /\ U8.v (get h1 output 2) = (U32.v m / pow2 16) % pow2 8
    /\ U8.v (get h1 output 3) = (U32.v m / pow2 24)  % pow2 8 ))
let rec bytes_of_uint32 output x =
  let b0 = uint32_to_uint8 (x) in
  let b1 = uint32_to_uint8 ((x >>^ 8ul)) in
  let b2 = uint32_to_uint8 ((x >>^ 16ul)) in
  let b3 = uint32_to_uint8 ((x >>^ 24ul)) in
  output.(0ul) <- b0;
  output.(1ul) <- b1;
  output.(2ul) <- b2;
  output.(3ul) <- b3

(* A form of memset, could go into some "Utils" functions module *)
//16-10-03 added functional step; made pre-condition tighter (sufficient for use in AEAD)
val memset: b:bytes -> z:u8 -> len:u32 -> STL unit
  (requires (fun h -> live h b /\ v len = length b))
  (ensures  (fun h0 _ h1 -> 
    live h1 b /\ modifies_1 b h0 h1 /\ 
    Seq.equal (as_seq h1 b) (Seq.create (v len) z)))
let rec memset b z len =
  if len = 0ul then ()
  else
  begin
    let h0 = ST.get() in
    let i = len -^ 1ul in
    memset (offset b 1ul) z i; // we should swap these two lines for tail recursion
    b.(0ul) <- z; 
    let h1 = ST.get() in 
    let s = as_seq h1 b in
    assert(Seq.index s 0 = z); // ...but this fails in the absence of framing
    assert(Seq.equal s (Seq.cons z (Seq.slice s 1 (v len))))
  end
