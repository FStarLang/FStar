module Crypto.Symmetric.PRF

(* This file models our idealization of symmetric ciphers used only in
   forward mode, including CHACHA20 and several variants of AES for
   for GCM or CCM, modellied as a PRF to build authenticated
   encryption.

   It models (an ad hoc variant of) the PRF security assumption:

   It captures the 3 different uses of the PRF in this construction:
   to generate the one-time MAC key, to generate a one-time-pad for
   encryption, and to generate a one-time-pad for decryption. *)

// 16-10-15 currently specialized to CHACHA20 and POLY1305 
// TODO improve agility (more i:id) and also support AES256 and AES128
// TODO add a shared MAC key (here or in AEAD)

open FStar.Ghost
open FStar.UInt8
open FStar.UInt32

open Crypto.Symmetric.Bytes
open Flag
open Plain

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
  
module MAC   = Crypto.Symmetric.Poly1305.MAC 
module Block = Crypto.Symmetric.Cipher

// PRF TABLE

let blocklen i = Block.blocklen (cipher_of_id i)
type block i = b:lbytes (v (blocklen i))
let keylen i = Block.keylen (cipher_of_id i)

(*
private let lemma_lengths (i:id) : Lemma(keylen i <^ blocklen i) = 
  match i.cipher with 
  | AES_256_GCM -> ()
  | CHACHA20_POLY1305 -> ()
*)

let id = i:Flag.id {i.cipher = CHACHA20_POLY1305} //16-10-15 temporary

// IDEALIZATION
// step 1. Flag.prf i relies on PRF just to get fresh MAC keys. 
// step 2. Flag.safeId i relies on authenticated encryption to get semantic encryption

private let sanity_check i = assert(safeId i ==> prf i)

// LIBRARY STUFF

type region = rgn:HH.rid {HS.is_eternal_region rgn}


// to be adjusted, controlling concrete bound.
//16-10-15 how to ensure it is reduced at compile-time?
let maxCtr i = 16384ul /^ blocklen i
type ctrT i = x:u32 {x <=^ maxCtr i}


// The PRF domain: an IV and a counter.

type domain (i:id) = { iv:Block.iv (cipher_of_id i); ctr:ctrT i} 
let incr (i:id) (x:domain i {x.ctr <^ maxCtr i}) = { iv = x.iv; ctr = x.ctr +^ 1ul }

val above: #i:id -> domain i -> domain i -> Tot bool
let above #i x z = x.iv = z.iv && x.ctr >=^ z.ctr

// the range of our PRF, after idealization and "reverse inlining."
// for one-time-pads, we keep both the plain and cipher blocks, instead of their XOR.

type smac (rgn:region) (i:id) x = mac: MAC.state (i,x.iv) { MAC.State.region mac = rgn }
noeq type otp (i:id) = | OTP: l:u32 {l <=^ blocklen i} -> plain i (v l) -> cipher:lbytes (v l) -> otp i

let range (mac_rgn:region) (i:id) (x:domain i): Type0 =
  if x.ctr = 0ul then smac mac_rgn i x
  else if safeId i then otp i
  else lbytes (v (blocklen i))

let domain_mac (i:id) = x:domain i{x.ctr = 0ul} 
let domain_otp (i:id) = x:domain i{x.ctr <> 0ul /\ safeId i}
let domain_blk (i:id) = x:domain i{x.ctr <> 0ul /\ ~ (safeId i)}

// explicit coercions
let macRange rgn (i:id) (x:domain_mac i) (z:range rgn i x) : smac rgn i x = z
let otpRange rgn (i:id) (x:domain_otp i) (z:range rgn i x) : otp i = z 
let blkRange rgn (i:id) (x:domain_blk i) (z:range rgn i x) : block i = z

noeq type entry (rgn:region) (i:id) =
  | Entry: x:domain i -> range:range rgn i x -> entry rgn i

let find (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain i) : option (range rgn i x) =
  match SeqProperties.seq_find (fun (e:entry rgn i) -> e.x = x) s with
  | Some e -> Some e.range
  | None   -> None
let find_mac #rgn (#i:id) s (x:domain_mac i) =
  match find s x with
  | Some v -> Some(macRange rgn i x v)
  | None   -> None
let find_otp #rgn (#i:id) s (x:domain_otp i) =
  match find s x with
  | Some v -> Some(otpRange rgn i x v)
  | None   -> None
let find_blk #rgn (#i:id) s (x:domain_blk i) =
  match find s x with
  | Some v -> Some (blkRange rgn i x v)
  | None   -> None

// The table exists only for idealization
// What's in the table stays there. And the table does not have two entries with the same x.
// TODO consider using a monotonic map to enforce those
let table_t rgn mac_rgn (i:id) = 
  if prf i then r:HS.ref (Seq.seq (entry mac_rgn i)) {HS.frameOf r = rgn}
  else unit

// the PRF instance, 
// including its key and memoization table (in rgn) 
// and its mac instances (below in mac_rgn)
// NOTE both regions are meant to be allocated at the writer. A bit dubious for the real key state.
noeq type state (i:id) =
  | State: #rgn: region ->
	   #mac_rgn: region{mac_rgn `HH.extends` rgn} ->
           // key is immutable once generated, we should make it private
           key: lbuffer (v (keylen i)) 
             {Buffer.frameOf key = rgn /\ ~(HS.MkRef.mm (Buffer.content key))} ->
           table: table_t rgn mac_rgn i ->
           state i

// boring...
val itable: i:id {prf i} -> s:state i 
  -> Tot (r:HS.ref (Seq.seq (entry s.mac_rgn i)) {HS.frameOf r = s.rgn})
let itable i s = s.table

val mktable: i:id {prf i} -> rgn:region -> mac_rgn:region{mac_rgn `HH.extends` rgn}
  -> r:HS.ref (Seq.seq (entry mac_rgn i)) {HS.frameOf r = rgn} -> Tot (table_t rgn mac_rgn i)
let mktable i rgn mac_rgn r = r 

val no_table: i:id {~(prf i)} -> rgn:region -> mac_rgn:region{mac_rgn `HH.extends` rgn} -> Tot (table_t rgn mac_rgn i)
let no_table i rgn mac_rgn = ()

val gen: rgn:region -> i:id -> ST (state i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 ->
    s.rgn == rgn /\ 
    (prf i ==> HS.sel h1 (itable i s) == Seq.createEmpty #(entry s.mac_rgn i))))
let gen rgn i =
  let mac_rgn : (r:region{r `HH.extends` rgn}) = new_region rgn in
  let key = Buffer.rcreate rgn 0uy (keylen i) in
  Bytes.random (v (keylen i)) key;
  let table: table_t rgn mac_rgn i =
    if prf i then 
      mktable i rgn mac_rgn (ralloc rgn (Seq.createEmpty #(entry mac_rgn i)))
    else ()
  in
  State #i #rgn #mac_rgn key table
// no need to demand prf i so far.

val coerce: rgn:region -> i:id{~(prf i)} -> key:lbuffer (v (keylen i)) -> ST (state i)
  (requires (fun h -> Buffer.live h key))
  (ensures  (fun h0 s h1 -> s.rgn == rgn))
let coerce rgn i key =
  let mac_rgn : (r:region{r `HH.extends` rgn}) = new_region rgn in
  let key_p = Buffer.rcreate rgn 0uy (keylen i) in
  Buffer.blit key 0ul key_p 0ul (keylen i);
  State #i #rgn #mac_rgn key_p (no_table i rgn mac_rgn)

// TODO leak, and eventually dynamic compromise.


(** computes a PRF block and copies its len first bytes to output *)

private val getBlock: 
  #i:id -> t:state i -> domain i -> len:u32 {len <=^ blocklen i} -> 
  output:lbuffer (v len) { Buffer.disjoint t.key output } -> STL unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 r h1 -> Buffer.live h1 output /\ Buffer.modifies_1 output h0 h1 ))
let getBlock #i t x len output =
  Buffer.recall t.key;
  Block.compute (cipher_of_id i) output t.key x.iv x.ctr len


// We encapsulate our 3 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table.
//
// For xor-based encryption,
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

// the first block (ctr=0) is used to generate a single-use MAC

val prf_mac: 
  i:id -> t:state i -> x:domain_mac i -> ST (MAC.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures (fun h0 mac h1 ->
    if prf i then
    ( let r = itable i t in
      match find_mac (HS.sel h0 r) x with // already in the table? 
      | Some mac' -> mac == mac' /\ h0 == h1 // when decrypting
      | None ->  // when encrypting, we get the stateful post of MAC.create             
        match find_mac (HS.sel h1 r) x with 
        | Some mac' -> 
	  mac == mac' /\ 
	  MAC.genPost0 (i,x.iv) t.mac_rgn h0 mac h1 /\
          HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\
	  HS.modifies_ref t.mac_rgn TSet.empty h0 h1
          //16-10-11 we miss a more precise clause capturing the table update   
        | None -> False )
    else (
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\
      HS.modifies_ref t.rgn TSet.empty h0 h1  /\
      HS.modifies_ref t.mac_rgn TSet.empty h0 h1 )))

#reset-options "--z3timeout 100"

let prf_mac i t x =
  let h0 = get () in
  Buffer.recall t.key;
  recall_region t.mac_rgn;
  let macId = (i,x.iv) in
  if prf i then
    begin
    let r = itable i t in
    recall r;
    let contents = !r in
    match find_mac contents x with
    | Some mac -> mac
    | None ->
      let mac = MAC.gen macId t.mac_rgn in
      r := SeqProperties.snoc contents (Entry x mac);
      assume false; 
      //16-10-16 framing after chang eto genPost0?
      //let h = ST.get() in assume(MAC(norm h mac.r));
      mac
    end
  else
    begin
    let keyBuffer = Buffer.rcreate t.mac_rgn 0uy (MAC.keylen i) in
    let h1 = ST.get() in
    getBlock t x (MAC.keylen i) keyBuffer;
    let h2 = ST.get() in
    Buffer.lemma_reveal_modifies_1 keyBuffer h1 h2;
    MAC.coerce macId t.mac_rgn keyBuffer
    end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private let extends #rgn #i s0 s1 x =
  let open FStar.Seq in 
  let open FStar.SeqProperties in 
  ( match find s0 x with 
    | Some _ -> s1 == s1 
    | None   -> exists (e:entry rgn i). e.x = x /\ s1 == snoc s0 e  )

// modifies a table (at most at x) and a buffer.
let modifies_x_buffer_1 #i (t:state i) x b h0 h1 = 
  Buffer.live h1 b /\ 
  (if prf i then 
    let r = itable i t in 
    let rb = Buffer.frameOf b in
    // can't use !{ t.rgn, rb}, why?
    let rgns = Set.union (Set.singleton #HH.rid t.rgn) (Set.singleton #HH.rid rb) in
    HS.modifies rgns h0 h1 /\
    HS.modifies_ref t.rgn !{HS.as_ref r} h0 h1 /\
    extends (HS.sel h0 r) (HS.sel h1 r) x /\
    Buffer.modifies_buf_1 rb b h0 h1 
  else
    Buffer.modifies_1 b h0 h1)

// real case + real use of memoized PRF output.
private val prf_blk: 
  i:id -> t:state i -> x:domain_blk i -> len:u32 {len <=^ blocklen i} -> 
  output:lbuffer (v len) {Buffer.frameOf output <> t.rgn} -> ST unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 _ h1 -> modifies_x_buffer_1 t x output h0 h1)) 

#reset-options "--z3timeout 100"

let prf_blk i t x len output =
  if prf i then
    begin
    let r = itable i t in 
    let contents = recall r; !r in
    let h0 = ST.get() in
    let block = 
      match find_blk contents x with 
      | Some block -> block
      | None ->
          let block = random_bytes (blocklen i) in
          r := SeqProperties.snoc contents (Entry x block);
          // assert(extends (HS.sel h0 r) (HS.sel h' r) x);
          block
    in
    let h1 = ST.get() in
    assert(extends (HS.sel h0 r) (HS.sel h1 r) x);
    store_bytes len output (Seq.slice block 0 (v len));
    let h2 = ST.get() in
    Buffer.lemma_reveal_modifies_1 output h1 h2
    end
  else
    getBlock t x len output


// reuse the same block for x and XORs it with ciphertext
val prf_dexor: 
  i:id -> t:state i -> x:domain i{x.ctr <> 0ul} -> l:u32 {l <=^ blocklen i} -> 
  plain:plainBuffer i (v l) -> cipher:lbuffer (v l) 
  { Buffer.disjoint (as_buffer plain) cipher /\
    Buffer.frameOf (as_buffer plain) <> t.rgn } -> ST unit
  (requires (fun h0 ->
     Plain.live h0 plain /\ Buffer.live h0 cipher /\ 
     (safeId i ==>
     ( match find_otp (HS.sel h0 (itable i t)) x with
       | Some (OTP l' p c) -> l == l' /\ c == sel_bytes h0 l cipher
       | None -> False ))))
  (ensures (fun h0 _ h1 ->
     let pb = as_buffer plain in 
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     (if prf i then 
       let r = itable i t in 
       if safeId i then
       ( match find_otp (HS.sel h1 r) x with
         | Some (OTP l' p c) -> l == l' /\ p == sel_plain h1 l plain /\ Buffer.modifies_1 pb h0 h1
         | None -> False )
       else modifies_x_buffer_1 t x pb h0 h1
     else Buffer.modifies_1 pb h0 h1 )))

let prf_dexor i t x l plain cipher =
  if safeId i then
    let r = itable i t in 
    let contents = recall r; !r in
    match find_otp contents x with
    | Some (OTP l' p c) -> 
        let h0 = ST.get() in
        Plain.store #i l plain p;
        let h1 = ST.get() in
        Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0 h1
  else
    let h0 = ST.get() in
    let plainrepr = bufferRepr #i #(v l) plain in
    assert(Buffer.disjoint plainrepr cipher);
    prf_blk i t x l plainrepr; 
    let h1 = ST.get() in
    assert(modifies_x_buffer_1 t x plainrepr h0 h1);
    (if prf i then recall (itable i t));
    Buffer.Utils.xor_bytes_inplace plainrepr cipher l;
    let h2 = ST.get() in
    Buffer.lemma_reveal_modifies_1 plainrepr h1 h2;
    assert(prf i ==> HS.sel h1 (itable i t) == HS.sel h2 (itable i t));
    assert(modifies_x_buffer_1 t x plainrepr h0 h2)

#set-options "--initial_fuel 1 --max_fuel 1"

private let lemma_snoc_found (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain i) (v:range rgn i x) : Lemma
  (requires (find s x == None))
  (ensures (find (SeqProperties.snoc s (Entry x v)) x == Some v))
  = ()

#reset-options "--z3timeout 100"

// generates a fresh block for x and XORs it with plaintext
val prf_enxor: 
  i:id -> t:state i -> x:domain i{x.ctr <> 0ul} -> l:u32 {l <=^ blocklen i} -> 
  cipher:lbuffer (v l) -> plain:plainBuffer i (v l) 
  {  Buffer.disjoint (as_buffer plain) cipher /\ 
     Buffer.frameOf (as_buffer plain) <> t.rgn /\ 
     Buffer.frameOf cipher <> t.rgn } -> ST unit
  (requires (fun h0 ->
     Plain.live h0 plain /\ Buffer.live h0 cipher /\
     (safeId i ==> find_otp #t.mac_rgn #i (HS.sel h0 t.table) x == None)))
  (ensures (fun h0 _ h1 ->
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     modifies_x_buffer_1 t x cipher h0 h1 /\
     (safeId i ==> 
       ( match find_otp #t.mac_rgn #i (HS.sel h1 t.table) x with
         | Some (OTP l' p c) -> l = l' /\ p == sel_plain h1 l plain /\ c == sel_bytes h1 l cipher
         | None   -> False ))))
         
let prf_enxor i t x l cipher plain =
  if safeId i then
    let r = itable i t in 
    let contents = recall r; !r in 
    let p = Plain.load #i l plain in
    let c = random_bytes l in // sample a fresh ciphertext block
    let newblock = OTP #i l p c in
    let contents' = SeqProperties.snoc contents (Entry x newblock) in
    lemma_snoc_found contents x newblock;
    assert(find_otp #t.mac_rgn #i contents x == None); 
    assert(find_otp #t.mac_rgn #i contents' x == Some newblock);

    let h0 = ST.get() in
    assert(p == sel_plain h0 l plain);
    store_bytes l cipher c;
    let h1 = ST.get() in
    Buffer.lemma_reveal_modifies_1 cipher h0 h1;
    assert(p == sel_plain h1 l plain);
    r := contents';
    let h2 = ST.get() in
    assert(p == sel_plain h2 l plain); //16-10-12  how to anti-alias a buffer?
    assert(modifies_x_buffer_1 t x cipher h0 h2)
  else
    let h0 = ST.get() in 
    let plainrepr = bufferRepr #i #(v l) plain in
    assert(Buffer.disjoint plainrepr cipher);
    prf_blk i t x l cipher;
    let h1 = ST.get() in
    assert(modifies_x_buffer_1 t x cipher h0 h1);
    (if prf i then recall (itable i t));
    Buffer.Utils.xor_bytes_inplace cipher plainrepr l;
    let h2 = ST.get() in
    Buffer.lemma_reveal_modifies_1 cipher h1 h2;
    assert(prf i ==> HS.sel h1 (itable i t) == HS.sel h2 (itable i t));
    assert(modifies_x_buffer_1 t x cipher h0 h2)
