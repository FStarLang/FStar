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
module Crypto.AEAD.Encoding 

// This file defines the encoding of additional data and ciphertext
// authenticated by the one-time MACs, and proves their injectivity properties. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open FStar.Math.Lib
open FStar.Math.Lemmas
open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag
open FStar.HyperStack.ST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

let alg (i:id) = cipherAlg_of_id i 

type rgn = rgn:HH.rid {HS.is_eternal_region rgn}

// concrete (somewhat arbitrary) bounds on inputs lengths
let txtmax = 16485ul
let aadmax = 2000ul

// placeholder for additional data
type adata = b:bytes { Seq.length b <= v aadmax} 
type cipher (i:id) (l:nat) = lbytes(l + v MAC.taglen)

type aadlen_32 = l:UInt32.t {l <=^ aadmax}
type txtlen_32 = l:UInt32.t {l <=^ txtmax}


//16-09-18 where is it in the libraries?
private let min (a:nat) (b:nat) : nat = if a <= b then a else b

val lemma_append_nil: #a:_ -> s:Seq.seq a -> Lemma (s == Seq.append s Seq.empty)
let lemma_append_nil #a s = assert (Seq.equal s (Seq.append s Seq.empty))


(* * *********************************************)
(* *            Encoding                         *)
(* * *********************************************)

let pad_0 b l = Seq.append b (Seq.create l 0uy)
 
// spec for encoding bytestrings into sequences of words. // Note the refined refinement interferes with type instantiation
val encode_bytes: txt:Seq.seq UInt8.t -> 
  GTot (r:MAC.text{Seq.length r = (Seq.length txt + 15)/16}) 
  (decreases (Seq.length txt))

// separated padding case to match imperative code
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then 
    Seq.empty
  else if l < 16 then
    Seq.create 1 (pad_0 txt (16 - l))
  else
    let txt0, txt = Seq.split txt 16 in
    Seq.snoc (encode_bytes txt) txt0

(* now intrinsic (easier to prove)
let rec lemma_encode_length txt: Lemma
  (ensures (Seq.length(encode_bytes txt) = (Seq.length txt + 15) / 16))
  (decreases (Seq.length txt)) =
  let l = Seq.length txt in 
  if l = 0 then ()
  else if l < 16 then assert(Seq.length(encode_bytes txt) = 1)
  else (
    let txt0, txt' = Seq.split txt 16 in
    lemma_encode_length txt';
    assert(Seq.length(encode_bytes txt) = 1 + Seq.length(encode_bytes txt')))
*)

(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

val lemma_pad_0_injective: b0:Seq.seq UInt8.t -> b1:Seq.seq UInt8.t -> l:nat -> Lemma
  (requires (pad_0 b0 l == pad_0 b1 l))
  (ensures  (b0 == b1))
let lemma_pad_0_injective b0 b1 l =
  Seq.lemma_append_inj b0 (Seq.create l 0uy) b1 (Seq.create l 0uy);
  Seq.lemma_eq_intro b0 b1

(* use the one in Poly1305.Spec:

// prime (do we prove it?)
let p_1305: p:nat{pow2 128 < p} =
  assert_norm (pow2 128 < pow2 130 - 5);
  pow2 130 - 5
val lemma_encode_injective: i:MAC.id -> w0:word -> w1:word -> Lemma
  (requires (length w0 == length w1 /\ MAC.encode i w0 == MAC.encode i w1))
  (ensures  (w0 == w1))
let lemma_encode_injective w0 w1 =
  let open FStar.Mul in 
  let l = length w0 in
  lemma_little_endian_is_bounded w0;
  lemma_little_endian_is_bounded w1;
  pow2_le_compat 128 (8 * l);
  lemma_mod_plus_injective p_1305 (pow2 (8 * l))
    (little_endian w0) (little_endian w1);
  assert (little_endian w0 == little_endian w1);
  Seq.lemma_eq_intro (Seq.slice w0 0 l) w0;
  Seq.lemma_eq_intro (Seq.slice w1 0 l) w1;
  lemma_little_endian_is_injective w0 w1 l
*)

val lemma_encode_bytes_injective: t0:Seq.seq UInt8.t -> t1:Seq.seq UInt8.t -> Lemma
  (requires Seq.length t0 == Seq.length t1 /\ encode_bytes t0 == encode_bytes t1)
  (ensures t0 == t1)
  (decreases (Seq.length t0))
let rec lemma_encode_bytes_injective t0 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else  if l < 16 then 
    let w0 = pad_0 t0 (16 - l) in 
    let w1 = pad_0 t1 (16 - l) in 
    assert(Seq.head (encode_bytes t0) == Seq.head (encode_bytes t1));
    lemma_pad_0_injective t0 t1 (16 - l)
  else
    let w0, t0' = Seq.split_eq t0 16 in
    let w1, t1' = Seq.split_eq t1 16 in
    Seq.lemma_eq_refl (encode_bytes t0) (encode_bytes t1);
    Seq.lemma_snoc_inj (encode_bytes t0') (encode_bytes t1') w0 w1 ;
    lemma_encode_bytes_injective t0' t1';
    Seq.lemma_eq_elim t0' t1'

#set-options "--z3rlimit 256"
// If the length is not a multiple of 16, pad to 16
// (we actually don't depend on the details of the padding)
val pad_16: b:lbuffer 16 -> len:UInt32.t { 0 < v len /\ v len <= 16 } -> STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> 
    Buffer.live h0 b /\
    Buffer.live h1 b /\ 
    Buffer.modifies_1 b h0 h1 /\ 
    Seq.equal (Buffer.as_seq h1 b) (pad_0 (Buffer.as_seq h0 (Buffer.sub b 0ul len)) (16 - v len))))
let pad_16 b len =
  memset (Buffer.offset b len) 0uy (16ul -^ len)

open FStar.HyperStack

let modifies_nothing (h:mem) (h':mem) : GTot Type0 =
  (forall rid. Set.mem rid (Map.domain h.h) ==>
    HH.modifies_rref rid Set.empty h.h h'.h
    /\ (forall (#a:Type) (b:Buffer.buffer a). 
      (Buffer.frameOf b == rid /\ Buffer.live h b ==> Buffer.equal h b h' b)))


// add variable-length bytes to a MAC accumulator, one 16-byte word at a time
private val add_bytes:
  #i: MAC.id ->
  st: CMA.state i ->
  acc: CMA.accBuffer i ->
  len: UInt32.t ->
  txt: lbuffer (v len) -> Stack unit
  (requires (fun h0 -> 
    Buffer.live h0 txt /\ 
    CMA.acc_inv st acc h0 /\
    Buffer.disjoint (MAC.as_buffer (CMA.abuf acc)) txt /\
    Buffer.disjoint CMA.(MAC.as_buffer st.r) txt /\
    (mac_log ==> Buffer.frameOf txt <> (CMA.alog acc).id  \/  Buffer.disjoint_ref_1 txt CMA.(alog acc)) ))
  (ensures (fun h0 () h1 -> 
    let b = CMA.(MAC.as_buffer (CMA.abuf acc)) in
    Buffer.live h1 txt /\ 
    CMA.acc_inv st acc h1 /\ //(1)
    (if mac_log then 
      let log = CMA.alog acc in
      let l0 = FStar.HyperStack.sel h0 log in
      let l1 = FStar.HyperStack.sel h1 log in
      Seq.equal l1 (Seq.append (encode_bytes (Buffer.as_seq h1 txt)) l0) /\ //(2) 
      CMA.modifies_buf_and_ref b log h0 h1 //(3)
    else 
      Buffer.modifies_1 b h0 h1 //(4)
      )))

// not sure why I need these lemmas; maybe just Z3 complexity
private let lemma_encode_loop (b:_ { Seq.length b >= 16 }) : Lemma
  ( encode_bytes b ==
    Seq.snoc 
      (encode_bytes (Seq.slice b 16 (Seq.length b))) 
      (Seq.slice b 0 16)) 
  =  ()

val lemma_encode_final: b:Seq.seq UInt8.t{0 <> Seq.length b /\ Seq.length b < 16} ->
  Lemma (Seq.equal (encode_bytes b) (Seq.create 1 (pad_0 b (16 - Seq.length b))))
let lemma_encode_final b = ()


#reset-options "--z3rlimit 140 --initial_fuel 0 --max_fuel 0"

let rec add_bytes #i st acc len txt =
  let h0 = ST.get() in 
  assert(mac_log ==> h0 `contains` (CMA.alog acc));
  push_frame();
  let h1 = ST.get() in
  CMA.frame_acc_inv st acc h0 h1;
  if len = 0ul then () else 
  if len <^ 16ul then 
      begin
        let w = Buffer.create 0uy 16ul in
        let h2 = ST.get() in 
        Buffer.lemma_reveal_modifies_0 h1 h2;
        Buffer.blit txt 0ul w 0ul len;
        pad_16 w len;
        let h3 = ST.get() in
        Buffer.lemma_reveal_modifies_1 w h2 h3;
        CMA.frame_acc_inv st acc h1 h3;
        CMA.update st acc w;
        let h4 = ST.get() in 
        if mac_log then
          begin // showing log := padded w :: log 
            let txt0 = Buffer.as_seq h0 txt in 
            let x = Buffer.as_seq h3 w in
            let log = CMA.alog acc in 
            let l0 = HS.sel h0 log in
            let l1 = HS.sel h1 log in
            let l3 = HS.sel h3 log in
            let l4 = HS.sel h4 log in
            assert(Seq.equal x (pad_0 txt0 (16 - v len)));
            assert(Seq.equal l4 (Seq.cons x l0));
            lemma_encode_final txt0;
            assert(Seq.equal l4 (Seq.append (encode_bytes txt0) l0))
          end
        else Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc))  h3 h4
      end
  else 
      begin
        let w = Buffer.sub txt 0ul 16ul in 
        let txt' = Buffer.offset txt 16ul in
        CMA.update st acc w;
        let h2 = ST.get() in 
        add_bytes st acc (len -^ 16ul) txt';
        let h3 = ST.get() in
        if mac_log 
        then begin // showing log := encode_bytes txt' @ [w] @ log 
          let txt0 = Buffer.as_seq h0 txt in 
          let txt1 = Buffer.as_seq h1 txt' in 
          let x = Buffer.as_seq h1 w in
          let log = CMA.alog acc in
          let l1 = HS.sel h1 log in
          let l2 = HS.sel h2 log in
          let l3 = HS.sel h3 log in
          assert(Seq.equal txt0 (Seq.append x txt1));
          lemma_encode_loop txt0;
          assert(Seq.equal l2 (Seq.cons x l1));
          assert(Seq.equal l3 (Seq.append (encode_bytes txt1) l2));
          Seq.append_cons_snoc (encode_bytes txt1) x l3;
          assert(Seq.equal l3 (Seq.append (encode_bytes txt0) l1))
        end
        else Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h1 h3
      end;
  let h5 = ST.get() in
  pop_frame();
  let h6 = ST.get() in
  CMA.frame_acc_inv st acc h5 h6;
  MAC.frame_sel_elem h5 h6 (CMA.abuf acc);
  if not mac_log then
    Buffer.lemma_intro_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h0 h6

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
private let encode_lengths_poly1305 (aadlen:UInt32.t) (plainlen:UInt32.t) : b:lbytes 16
  { v aadlen = little_endian (Seq.slice b 0 4) /\
    v plainlen = little_endian (Seq.slice b 8 12) } = 
  let b0 = Seq.create 4 0uy in 
  let ba = uint32_bytes 4ul aadlen in
  let bp = uint32_bytes 4ul plainlen in 
  let open FStar.Seq in 
  let b = ba @| b0 @| bp @| b0 in
  Seq.append_slices ba (b0 @| bp @| b0);
  Seq.append_slices b0 (bp @| b0);
  Seq.append_slices bp b0;
  b
//16-11-01 unclear why verification is slow above, fast below
#reset-options

#set-options "--z3rlimit 200"
private val store_lengths_poly1305: aadlen:UInt32.t ->  plainlen:UInt32.t -> w:lbuffer 16 ->
  StackInline unit 
  (requires (fun h0 -> Buffer.live h0 w /\ Buffer.as_seq h0 w = Seq.create 16 0uy))
  (ensures (fun h0 _ h1 -> 
    Buffer.live h1 w /\ Buffer.modifies_1 w h0 h1 /\
    Seq.equal (Buffer.as_seq h1 w) (encode_lengths_poly1305 aadlen plainlen)))
let store_lengths_poly1305 aadlen plainlen w = 
  let w0 = Buffer.sub w 0ul 4ul in
  let w1 = Buffer.sub w 4ul 4ul in
  let w2 = Buffer.sub w 8ul 4ul in
  let w3 = Buffer.sub w 12ul 4ul in
  store_uint32 4ul w0 aadlen;
  store_uint32 4ul w2 plainlen;
  let h1 = ST.get() in 
  lemma_little_endian_inj (uint32_bytes 4ul aadlen) (Buffer.as_seq h1 w0);
  assert(Seq.equal (Buffer.as_seq h1 w1) (Seq.create 4 0uy));
  lemma_little_endian_inj (uint32_bytes 4ul plainlen) (Buffer.as_seq h1 w2);
  assert(Seq.equal (Buffer.as_seq h1 w3) (Seq.create 4 0uy))

open FStar.Mul
//16-10-31 confirm FIPS length formatting for GHASH (inferred from test vectors)
private let encode_lengths_ghash (aadlen:aadlen_32) (txtlen:txtlen_32) : b:lbytes 16
  { 8 * v aadlen = big_endian (Seq.slice b 4 8) /\
    8 * v txtlen = big_endian (Seq.slice b 12 16) } =
  let open FStar.Seq in 
  let b0 = create 4 0uy in 
  let ba = uint32_be 4ul (8ul *^ aadlen) in
  let bp = uint32_be 4ul (8ul *^ txtlen) in 
  let b = b0 @| ba @| b0 @| bp in
  Seq.append_slices b0 (ba @| b0 @| bp);
  Seq.append_slices ba (b0 @| bp);
  Seq.append_slices b0 bp;
  b

private val store_lengths_ghash: aadlen:aadlen_32 ->  txtlen:txtlen_32  -> w:lbuffer 16 ->
  StackInline unit 
  (requires (fun h0 -> Buffer.live h0 w /\ Buffer.as_seq h0 w = Seq.create 16 0uy))
  (ensures (fun h0 _ h1 -> 
    Buffer.live h1 w /\ Buffer.modifies_1 w h0 h1 /\
    Seq.equal (Buffer.as_seq h1 w) (encode_lengths_ghash aadlen txtlen)))
let store_lengths_ghash aadlen txtlen w = 
  let w0 = Buffer.sub w 0ul 4ul in
  let w1 = Buffer.sub w 4ul 4ul in
  let w2 = Buffer.sub w 8ul 4ul in
  let w3 = Buffer.sub w 12ul 4ul in
  store_big32 4ul w1 (8ul *^ aadlen);
  store_big32 4ul w3 (8ul  *^ txtlen);
  let h1 = ST.get() in 
  assert(Seq.equal (Buffer.as_seq h1 w0) (Seq.create 4 0uy));
  lemma_big_endian_inj (uint32_be 4ul (8ul *^ aadlen)) (Buffer.as_seq h1 w1);
  assert(Seq.equal (Buffer.as_seq h1 w2) (Seq.create 4 0uy));
  lemma_big_endian_inj (uint32_be 4ul (8ul *^ txtlen)) (Buffer.as_seq h1 w3)

private let encode_lengths (i:id) (aadlen:aadlen_32) (txtlen:txtlen_32) : lbytes 16 =
  match macAlg_of_id i with 
  | POLY1305 -> encode_lengths_poly1305 aadlen txtlen 
  | GHASH -> encode_lengths_ghash aadlen txtlen

let encode_both (i:id) (aadlen:aadlen_32) (aad:lbytes (v aadlen)) (txtlen:txtlen_32) (cipher:lbytes (v txtlen)) :
  GTot (e:MAC.text {Seq.length e > 0 /\ Seq.head e = encode_lengths i aadlen txtlen}) = 
  Seq.cons (encode_lengths i aadlen txtlen)
    (Seq.append 
      (encode_bytes cipher) 
      (encode_bytes aad))

let lemma_encode_both_inj i (al0:aadlen_32) (pl0:txtlen_32) (al1:aadlen_32) (pl1:txtlen_32)
  (a0:lbytes(v al0)) (p0:lbytes(v pl0)) (a1:lbytes(v al1)) (p1:lbytes (v pl1)) : Lemma
  (requires encode_both i al0 a0 pl0 p0 = encode_both i al1 a1 pl1 p1)
  (ensures al0 = al1 /\ pl0 = pl1 /\ a0 = a1 /\ p0 = p1) = 

  let open FStar.Seq in 
  let w0 = encode_lengths i al0 pl0 in 
  let w1 = encode_lengths i al1 pl1 in
  //assert(encode w0 = encode w1);
  // lemma_encode_injective w0 w1; 
  //assert(al0 = al1 /\ pl0 = pl1);
  let ea0 = encode_bytes a0 in
  let ea1 = encode_bytes a1 in
  let ep0 = encode_bytes p0 in
  let ep1 = encode_bytes p1 in
  //assert(length ep0 = length ep1);
  //assert(encode_both al0 pl0 a0 p0 = cons (encode w0) (ep0 @| ea0));
  //assert(encode_both al1 pl1 a1 p1 = cons (encode w1) (ep1 @| ea1));
  lemma_append_inj (create 1 w0) (ep0 @| ea0) (create 1 w1) (ep1 @| ea1);
  //assert( ep0 @| ea0 = ep1 @| ea1);
  lemma_append_inj ep0 ea0 ep1 ea1;
  //assert(ep0 == ep1 /\ ea0 == ea1);
  lemma_encode_bytes_injective p0 p1;
  lemma_encode_bytes_injective a0 a1

val accumulate: 
  #i: MAC.id -> st: CMA.state i -> 
  aadlen:aadlen_32 -> aad:lbuffer (v aadlen) ->
  txtlen:txtlen_32 -> cipher:lbuffer (v txtlen) -> 
  StackInline (CMA.accBuffer i)   // StackInline required for stack-allocated accumulator
  (requires (fun h0 -> 
    CMA.(MAC.norm h0 st.r) /\
    Buffer.live h0 aad /\ 
    Buffer.live h0 cipher /\ 
    Buffer.disjoint_2 CMA.(MAC.as_buffer st.r) aad cipher))
  (ensures (fun h0 a h1 -> 
    Buffer.modifies_0 h0 h1 /\ // modifies only fresh buffers on the current stack
    ~ (h0 `Buffer.contains` CMA.(MAC.as_buffer (abuf a))) /\
    Buffer.live h1 aad /\ 
    Buffer.live h1 cipher /\
    Buffer.frameOf CMA.(MAC.as_buffer (abuf a)) = h1.tip /\
    CMA.acc_inv st a h1 /\
    (if mac_log then
        let log = CMA.alog a in
        //16-12-15 settle for a weaker property? modifies_nothing h0 h1 /\ 
        FStar.HyperStack.sel h1 log == encode_both (fst i) aadlen (Buffer.as_seq h1 aad) txtlen (Buffer.as_seq h1 cipher)
      else
        Buffer.modifies_0 h0 h1)))

// 20170313 JP: this verifies on my OSX laptop but not on the CI machine. See
// #893
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 2048 --lax"
let accumulate #i st aadlen aad txtlen cipher  = 
  let h = ST.get() in 
  let acc = CMA.start st in
  let h0 = ST.get() in
  //assert(mac_log ==> h0 `contains` (CMA.alog acc));
  Buffer.lemma_reveal_modifies_0 h h0;
  //assert (Buffer.disjoint_2 (MAC.as_buffer (CMA.(abuf acc))) aad cipher);
  add_bytes st acc aadlen aad;
  let h1 = ST.get() in 
  add_bytes st acc txtlen cipher;
  let h2 = ST.get() in 
  let final_word = Buffer.create 0uy 16ul in 
  let h3 = ST.get() in
  Buffer.lemma_reveal_modifies_0 h2 h3;
  //assert(mac_log ==> h3 `contains` (CMA.alog acc)); 
  let id, _ = i in  // JP: removed a call to Prims.fst
  ( match macAlg_of_id id with 
    | POLY1305 -> store_lengths_poly1305 aadlen txtlen final_word
    | GHASH -> store_lengths_ghash aadlen txtlen final_word );
  let h4 = ST.get() in 
  Buffer.lemma_reveal_modifies_1 final_word h3 h4;
  CMA.frame_acc_inv st acc h2 h3;
  CMA.frame_acc_inv st acc h3 h4;
  CMA.update st acc final_word;
  let h5 = ST.get() in 

  if mac_log then 
    begin
      let open FStar.Seq in 
      let al = CMA.alog acc in
      let cbytes = Buffer.as_seq h cipher in 
      let abytes = Buffer.as_seq h aad in 
      let lbytes = Buffer.as_seq h4 final_word in 
      assert(equal (HS.sel h0 al) Seq.empty);
      lemma_append_nil (encode_bytes abytes);
      assert(equal (HS.sel h1 al) (encode_bytes abytes));
      assert(equal (HS.sel h2 al) (encode_bytes cbytes @| encode_bytes abytes));
      assert(equal (HS.sel h5 al) (Seq.cons lbytes (encode_bytes cbytes @| encode_bytes abytes)));
      assert(equal (HS.sel h5 al) (encode_both (fst i) aadlen abytes txtlen cbytes));

      //16-12-15 can't prove Buffer.modifies_0 from current CMA posts?
      assert(HS.modifies_one h.tip h h0);
      //assume(HS.modifies_one h.tip h0 h2); //NS: cf. issue #788 (known limitation)
      assert(HS.modifies_one h.tip h2 h3);
      assert(HS.modifies_one h.tip h3 h4);
      //assume(HS.modifies_one h.tip h4 h5); //NS: cf. issue #788 (known limitation)
      assert(HS.modifies_one h.tip h h5);
      assert(Buffer.modifies_buf_0 h.tip h h5);
      Buffer.lemma_intro_modifies_0 h h5
    end
  else 
    begin
      Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.(abuf acc))) h0 h2;
      Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc))  h4 h5
    end;
  acc
