module Crypto.AEAD.Encoding 

// This file defines the encoding of additional data and ciphertext
// authenticated by the one-time MACs, and their injectivity properties. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open FStar.Math.Lib
open FStar.Math.Lemmas
open Crypto.Symmetric.Bytes
open Plain
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HH.rid {HS.is_eternal_region rgn}

//16-10-12 TEMPORARY, while PRF remains somewhat CHACHA-specific
let id = i:id {i.cipher = CHACHA20_POLY1305}

let alg (i:id) = cipher_of_id i 

type rgn = rgn:HH.rid {HS.is_eternal_region rgn}
    
type tagB i = lbuffer ( v(Spec.taglen i))

// placeholder for additional data
let aadmax = 2000ul
type adata = b:bytes { Seq.length b <= v aadmax} 
type cipher (i:id) (l:nat) = lbytes(l + v (Spec.taglen i))

// copied from Poly1305.Spec

(* * *********************************************)
(* *            Encoding                         *)
(* * *********************************************)

type elem = Spec.elem 

let encode (b:bytes {Seq.length b <= 16}) : Tot elem = Spec.encode b 

// a spec for encoding and padding, convenient for injectivity proof
let pad_0 b l = Seq.append b (Seq.create l 0uy)

val encode_pad: prefix:Seq.seq elem -> txt:Seq.seq UInt8.t -> GTot (Seq.seq elem) 
  (decreases (Seq.length txt))
let rec encode_pad prefix txt =
  let l = Seq.length txt in
  if l = 0 then prefix
  else if l < 16 then
    let w = txt in
    SeqProperties.snoc prefix (encode w)
  else
    begin
    let w, txt = SeqProperties.split txt 16 in
    let prefix = SeqProperties.snoc prefix (encode w) in
    encode_pad prefix txt
    end

//16-09-18 where is it in the libraries??
private let min (a:nat) (b:nat) : nat = if a <= b then a else b

//16-10-15 simpler variant? rediscuss injectivity.
val encode_bytes: txt:Seq.seq UInt8.t -> Tot (Seq.seq elem) (decreases (Seq.length txt))
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then 
    Seq.createEmpty
  else 
    let l0 = min l 16 in
    let txt0, txt = SeqProperties.split txt l0 in
    let w = pad_0 txt0 (16 - l0) in 
    SeqProperties.cons (encode w) (encode_bytes txt)

#reset-options "--lax"
let rec lemma_encode_length txt: Lemma
  (ensures (Seq.length(encode_bytes txt) = (Seq.length txt + 15) / 16))
  (decreases (Seq.length txt))
=
  let l = Seq.length txt in 
  if l = 0 then ()
  else if l < 16 then assert(Seq.length(encode_bytes txt) = 1)
  else (
    let txt0, txt' = SeqProperties.split txt 16 in
    lemma_encode_length txt'; //NS: this is provable, but it takes 4mins for Z3 to prove; disabling it until we can find a better, faster proof
    assume false;
    assert(Seq.length(encode_bytes txt) = 1 + Seq.length(encode_bytes txt')))

#reset-options
(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

open FStar.Seq

// prime (do we prove it?)
let p_1305: p:nat{pow2 128 < p} =
  assert_norm (pow2 128 < pow2 130 - 5);
  pow2 130 - 5

val lemma_pad_0_injective: b0:Seq.seq UInt8.t -> b1:Seq.seq UInt8.t -> l:nat -> Lemma
  (requires (pad_0 b0 l == pad_0 b1 l))
  (ensures  (b0 == b1))
let lemma_pad_0_injective b0 b1 l =
  SeqProperties.lemma_append_inj b0 (Seq.create l 0uy) b1 (Seq.create l 0uy);
  Seq.lemma_eq_intro b0 b1

val lemma_encode_injective: w0:word -> w1:word -> Lemma
  (requires (length w0 == length w1 /\ encode w0 == encode w1))
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

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

assume val lemma_encode_bytes_injective: t0:Seq.seq UInt8.t -> t1:Seq.seq UInt8.t -> Lemma
  (requires length t0 == length t1 /\ encode_bytes t0 == encode_bytes t1)
  (ensures t0 == t1)
  (decreases (Seq.length t0))
(*
let rec lemma_encode_bytes_injective t0 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else if l < 16 then
    begin
    lemma_index_create 1 (encode t0) 0;
    lemma_index_create 1 (encode t1) 0;
    lemma_encode_injective t0 t1
    end
  else
    begin
    let w0, t0' = SeqProperties.split_eq t0 16 in
    let w1, t1' = SeqProperties.split_eq t1 16 in
    let p0' = Seq.create 1 (encode w0) in
    let p1' = Seq.create 1 (encode w1) in
    assert (encode_pad p0' t0' == encode_pad p1' t1');
    lemma_encode_bytes_injective t0' t1';
    lemma_index_create 1 (encode w0) 0;
    lemma_index_create 1 (encode w1) 0;
    lemma_encode_injective w0 w1
    end
*)

val lemma_encode_pad_injective: p0:Seq.seq elem -> t0:Seq.seq UInt8.t -> p1:Seq.seq elem -> t1:Seq.seq UInt8.t -> Lemma
  (requires length t0 == length t1 /\ encode_pad p0 t0 == encode_pad p1 t1)
  (ensures  p0 == p1 /\ t0 == t1)
  (decreases (Seq.length t0))
let rec lemma_encode_pad_injective p0 t0 p1 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else if l < 16 then
    begin
    SeqProperties.lemma_append_inj
      p0 (Seq.create 1 (encode t0))
      p1 (Seq.create 1 (encode t1));
    lemma_index_create 1 (encode t0) 0;
    lemma_index_create 1 (encode t1) 0;
    lemma_encode_injective t0 t1
    end
  else
    begin
    let w0, t0' = SeqProperties.split_eq t0 16 in
    let w1, t1' = SeqProperties.split_eq t1 16 in
    let p0' = SeqProperties.snoc p0 (encode w0) in
    let p1' = SeqProperties.snoc p1 (encode w1) in
    assert (encode_pad p0' t0' == encode_pad p1' t1');
    lemma_encode_pad_injective p0' t0' p1' t1';
    SeqProperties.lemma_append_inj
      p0 (Seq.create 1 (encode w0))
      p1 (Seq.create 1 (encode w1));
    lemma_index_create 1 (encode w0) 0;
    lemma_index_create 1 (encode w1) 0;
    lemma_encode_injective w0 w1
    end

val encode_pad_empty: prefix:Seq.seq elem -> txt:Seq.seq UInt8.t -> Lemma
  (requires Seq.length txt == 0)
  (ensures  encode_pad prefix txt == prefix)
let encode_pad_empty prefix txt = ()

val encode_pad_snoc: prefix:Seq.seq elem -> txt:Seq.seq UInt8.t -> w:lbytes 16 -> Lemma
  (encode_pad (SeqProperties.snoc prefix (encode w)) txt ==
   encode_pad prefix (append w txt))
let encode_pad_snoc prefix txt w =
  Seq.lemma_len_append w txt;
  assert (16 <= Seq.length (append w txt));
  let w', txt' = SeqProperties.split (append w txt) 16 in
  let prefix' = SeqProperties.snoc prefix (encode w') in
  Seq.lemma_eq_intro w w';
  Seq.lemma_eq_intro txt txt'

// If the length is not a multiple of 16, pad to 16
// (we actually don't depend on the details of the padding)
val pad_16: b:lbuffer 16 -> len:UInt32.t { 0 < v len /\ v len <= 16 } -> STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 -> 
    Buffer.live h0 b /\
    Buffer.live h1 b /\ 
    Buffer.modifies_1 b h0 h1 /\ 
    Seq.equal (Buffer.as_seq h1 b) (Seq.append (Buffer.as_seq h0 (Buffer.sub b 0ul len)) (Seq.create (16 - v len) 0uy)))) 
let pad_16 b len =
  memset (Buffer.offset b len) 0uy (16ul -^ len)

open FStar.HyperStack

// add variable-length bytes to a MAC accumulator, one 16-byte word at a time
private val add_bytes:
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.itext -> 
  a : MAC.accB i ->
  len: UInt32.t ->
  txt:lbuffer (v len) -> STL MAC.itext
  (requires (fun h0 -> 
    Buffer.live h0 txt /\ MAC.acc_inv st l0 a h0))
  (ensures (fun h0 l1 h1 -> 
    Buffer.modifies_1 a h0 h1 /\ 
    Buffer.live h1 txt /\ MAC.acc_inv st l1 a h1 /\
    (mac_log ==> l1 == Seq.append (encode_bytes (Buffer.as_seq h1 txt)) l0)
    ))

let rec add_bytes #i st log a len txt =
  assume false; //TODO after specifying MAC.add
  push_frame();
  let r = 
    if len = 0ul then log
    else if len <^ 16ul then 
      begin
        let w = Buffer.create 0uy 16ul in
        Buffer.blit txt 0ul w 0ul len;
        pad_16 w len;
        MAC.add st log a w
      end
    else 
      begin
        let w = Buffer.sub txt 0ul 16ul in 
        let log = MAC.add st log a w in
        add_bytes st log a (len -^ 16ul) (Buffer.offset txt 16ul)
      end
  in
  pop_frame(); r

//16-10-16 TODO in SeqProperties
assume val lemma_append_slices: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma
  (ensures 
    ( s1 == Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)
    /\ s2 == Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length s1 + Seq.length s2))
    /\ (forall (i:nat) (j:nat).
       i <= j /\ j <= Seq.length s2 ==>
       Seq.slice s2 i j == Seq.slice (Seq.append s1 s2) (Seq.length s1 + i) (Seq.length s1 + j)))

assume val lemma_append_nil: #a:_ -> s:Seq.seq a -> 
  Lemma (s == Seq.append s Seq.createEmpty)
#set-options "--lax"
private let encode_lengths (aadlen:UInt32.t) (plainlen:UInt32.t) : b:lbytes 16
  { v aadlen = little_endian (Seq.slice b 0 4) /\
    v plainlen = little_endian (Seq.slice b 8 12) } = 
  let b0 = Seq.create 4 0uy in 
  let ba = uint32_bytes 4ul aadlen in
  let bp = uint32_bytes 4ul plainlen in 
  let open FStar.Seq in 
  let b = ba @| b0 @| bp @| b0 in
  lemma_append_slices ba (b0 @| bp @| b0);
  lemma_append_slices b0 (bp @| b0);
  lemma_append_slices bp b0;
  b

#reset-options
let encode_both aadlen (aad:lbytes (v aadlen)) clen (cipher:lbytes (v clen)) :
  e:Seq.seq elem {Seq.length e > 0 /\ SeqProperties.head e = encode(encode_lengths aadlen clen)} = 
  SeqProperties.cons (encode(encode_lengths aadlen clen))
    (Seq.append 
      (encode_bytes cipher) 
      (encode_bytes aad))

let field i = match alg i with 
  | Cipher.CHACHA20 -> elem
  | Cipher.AES256   -> lbytes (v Crypto.Symmetric.GF128.len) // not there yet

#set-options "--prn"
let field_encode (i:id) (aad:adata) (#l2:UInt32.t) (cipher:lbytes (v l2)) : GTot (Seq.seq (field i)) =
  match alg i with 
  | Cipher.CHACHA20 -> 
    encode_both (FStar.UInt32.uint_to_t (Seq.length aad)) aad l2 cipher
  | _ -> 
   //TODO
    Seq.createEmpty

let lemma_encode_both_inj al0 pl0 al1 pl1 
  (a0:lbytes(v al0)) (p0:lbytes(v pl0)) (a1:lbytes(v al1)) (p1:lbytes (v pl1)) : Lemma
  (requires encode_both al0 a0 pl0 p0 = encode_both al1 a1 pl1 p1)
  (ensures al0 = al1 /\ pl0 = pl1 /\ a0 = a1 /\ p0 = p1) = 

  let open FStar.Seq in 
  let open FStar.SeqProperties in
  let w0 = encode_lengths al0 pl0 in 
  let w1 = encode_lengths al1 pl1 in
  //assert(encode w0 = encode w1);
  lemma_encode_injective w0 w1; 
  //assert(al0 = al1 /\ pl0 = pl1);
  let ea0 = encode_bytes a0 in
  let ea1 = encode_bytes a1 in
  let ep0 = encode_bytes p0 in
  let ep1 = encode_bytes p1 in
  lemma_encode_length p0;
  lemma_encode_length p1;
  //assert(length ep0 = length ep1);
  //assert(encode_both al0 pl0 a0 p0 = cons (encode w0) (ep0 @| ea0));
  //assert(encode_both al1 pl1 a1 p1 = cons (encode w1) (ep1 @| ea1));
  lemma_append_inj (create 1 (encode w0)) (ep0 @| ea0) (create 1 (encode w1)) (ep1 @| ea1);
  //assert( ep0 @| ea0 = ep1 @| ea1);
  lemma_append_inj ep0 ea0 ep1 ea1;
  //assert(ep0 == ep1 /\ ea0 == ea1);
  lemma_encode_bytes_injective p0 p1;
  lemma_encode_bytes_injective a0 a1

val accumulate: 
  #i: MAC.id -> st: MAC.state i -> 
  aadlen:UInt32.t -> aad:lbuffer (v aadlen) ->
  plainlen:UInt32.t -> cipher:lbuffer (v plainlen) -> StackInline (MAC.itext * MAC.accB i)
  (requires (fun h0 -> 
    MAC(Buffer.live h0 st.r /\ norm h0 st.r) /\
    Buffer.live h0 aad /\ Buffer.live h0 cipher))
  (ensures (fun h0 (l,a) h1 -> 
    Buffer.modifies_0 h0 h1 /\ // modifies only fresh buffers on the current stack
    ~ (h0 `Buffer.contains` a) /\
    Buffer.live h1 aad /\ Buffer.live h1 cipher /\
    MAC.acc_inv st l a h1 /\
    (mac_log ==> l == encode_both aadlen (Buffer.as_seq h1 aad) plainlen (Buffer.as_seq h1 cipher))))
  // StackInline required for stack-allocated accumulator
  
let accumulate #i st (aadlen:UInt32.t) (aad:lbuffer (v aadlen))
  (plainlen:UInt32.t) (cipher:lbuffer (v plainlen)) = 

  let h = ST.get() in 
  let acc = MAC.start st in
  let h0 = ST.get() in
  Buffer.lemma_reveal_modifies_0 h h0;
  //16-10-16 :(
  assume (Buffer.disjoint aad acc /\ Buffer.disjoint cipher acc);

  let l = MAC.text_0 in 
  let l = add_bytes st l acc aadlen aad in
  let h1 = ST.get() in 
  Buffer.lemma_reveal_modifies_1 acc h0 h1;
  assert(mac_log ==> l = Seq.append(encode_bytes (Buffer.as_seq h1 aad)) MAC.text_0);

  assume false;//16-10-16 WIP
  // if mac_log then lemma_append_nil elem l;
  // assert(mac_log ==> l = encode_bytes (Buffer.as_seq h1 aad));
  let l = add_bytes st l acc plainlen cipher in 
  let h = ST.get() in 
  assert(mac_log ==> l = Seq.append (encode_bytes (Buffer.as_seq h cipher)) (encode_bytes (Buffer.as_seq h aad)));

  let l = 
    let final_word = Buffer.create 0uy 16ul in 
    store_uint32 4ul (Buffer.sub final_word 0ul 4ul) aadlen;
    store_uint32 4ul (Buffer.sub final_word 8ul 4ul) plainlen;
    let h = ST.get() in 
    assert(encode_lengths aadlen plainlen = Buffer.as_seq h final_word);
    MAC.add st l acc final_word in
  l, acc
