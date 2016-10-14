module Crypto.Symmetric.PRF

(* This file models our idealization of CHACHA20 (and soon any other
   cipher used only in forward mode, such as AES for GCM or CCM)
   as a PRF to build authenticated encryption.

   It models (an ad hoc variant of) the PRF security assumption:

   It captures the 3 different uses of the PRF in this construction:
   to generate the one-time MAC key, to generate a one-time-pad for
   encryption, and to generate a one-time-pad for decryption. *)

// TODO improve agility (more i:id) and also support AES
// TODO add pre- to statically prevent counter overflows

open FStar.HST
open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.HST.Monotonic.RRef

open Crypto.Symmetric.Bytes // including library stuff
open Flag
open Plain

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
  
module MAC   = Crypto.Symmetric.Poly1305.MAC
module Block = Crypto.Symmetric.Cipher

let prfa = Block.CHACHA20

let id = Flag.id 


// IDEALIZATION
// step 1. Flag.prf i relies on PRF just to get fresh MAC keys. 
// step 2. Flag.safeId i relies on authenticated encryption to get semantic encryption

private let sanity_check i = assert(safeId i ==> prf i)


// LIBRARY STUFF

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

type region = rgn:HH.rid {HS.is_eternal_region rgn}

// PRF TABLE

let maxCtr = 2000ul // to be adjusted, controlling concrete bound.
type ctrT = x:u32 {x <=^ maxCtr}


// used only ideally; noeq is painful here.

type domain = { iv:Block.iv prfa; ctr:ctrT } // could move to concrete CHACHA20
let incr (x:domain {x.ctr <^ maxCtr})  = { iv = x.iv; ctr = x.ctr +^ 1ul }


val above: domain -> domain -> Tot bool
let above x z = x.iv = z.iv && x.ctr >=^ z.ctr

let blocklen = Block.blocklen prfa
let block = b:bytes {Seq.length b = v blocklen}

let keylen = Block.keylen prfa

// the range of our PRF, after idealization and "reverse inlining."
// for one-time-pads, we keep both the plain and cipher blocks, instead of their XOR.

type smac (rgn:region) i x = mac: MAC.state (i,x.iv) { MAC.State.region mac = rgn }
noeq type otp i = | OTP: l:u32 {l <=^ blocklen} -> plain i (v l) -> cipher:lbytes (v l) -> otp i

let range (rgn:region) (i:id) (x:domain): Type0 =
  if x.ctr = 0ul then smac rgn i x
  else if safeId i then otp i
  else lbytes (v blocklen)

// explicit coercions
let macRange rgn i (x:domain{x.ctr = 0ul}) (z:range rgn i x) : smac rgn i x = z
let otpRange rgn i (x:domain{x.ctr <> 0ul /\ safeId i}) (z:range rgn i x) : otp i = z 
let blkRange rgn i (x:domain{x.ctr <> 0ul /\ ~ (safeId i)}) (z:range rgn i x) : lbytes (v blocklen) = z

noeq type entry (rgn:region) (i:id) =
  | Entry: x:domain -> range:range rgn i x -> entry rgn i

let find (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) : option (range rgn i x) =
  match SeqProperties.seq_find (fun (e:entry rgn i) -> e.x = x) s with
  | Some e -> Some e.range
  | None   -> None
let find_mac #rgn #i s (x:domain{x.ctr=0ul}) =
  match find s x with
  | Some v -> Some(macRange rgn i x v)
  | None   -> None
let find_otp #rgn #i s (x:domain{x.ctr<>0ul /\ safeId i}) =
  match find s x with
  | Some v -> Some(otpRange rgn i x v)
  | None   -> None
let find_blk #rgn #i s (x:domain{x.ctr<>0ul /\ ~(safeId i)}) =
  match find s x with
  | Some v -> Some (blkRange rgn i x v)
  | None   -> None

// The table exists only for idealization
// TODO it should be a monotonic map: what's in the table stays there. 
let table_t rgn i = 
  if prf i then r:HS.ref (Seq.seq (entry rgn i)) {HS.frameOf r = rgn}
  else unit

// the PRF instance, including its key and memoization table
// TODO separate on rw, with multiple readers?
noeq type state (i:id) =
  | State: #rgn: region -> 
           // key is immutable once generated, we should make it private
           key: lbuffer (v (Block.keylen prfa)) 
             {Buffer.frameOf key = rgn /\ ~(HS.MkRef.mm (Buffer.content key))} ->
           table: table_t rgn i ->
           state i

// boring...
val itable: i:id {prf i} -> s:state i 
  -> Tot (r:HS.ref (Seq.seq (entry s.rgn i)) {HS.frameOf r = s.rgn})
let itable i s = s.table

val mktable: i:id {prf i} -> rgn:region 
  -> r:HS.ref (Seq.seq (entry rgn i)) {HS.frameOf r = rgn} -> Tot (table_t rgn i)
let mktable i rgn r = r 

val no_table: i:id {~(prf i)} -> rgn:region -> Tot (table_t rgn i)
let no_table i rgn = ()


val gen: rgn:region -> i:id -> ST (state i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 ->
    s.rgn == rgn /\ 
    (prf i ==> HS.sel h1 (itable i s) == Seq.createEmpty #(entry rgn i))))
let gen rgn i =
  let key = Buffer.rcreate rgn 0uy (Block.keylen prfa) in
  Bytes.random (v (Block.keylen prfa)) key;
  let table: table_t rgn i =
    if prf i then mktable i rgn (ralloc rgn (Seq.createEmpty #(entry rgn i))) 
    else () 
  in
  State #i #rgn key table
// no need to demand prf i so far.

val coerce: rgn:region -> i:id{~(prf i)} -> key:lbuffer (v keylen) -> ST (state i)
  (requires (fun h -> Buffer.live h key))
  (ensures  (fun h0 s h1 -> s.rgn == rgn))
let coerce rgn i key =
  let key_p = Buffer.rcreate rgn 0uy (Block.keylen prfa) in
  Buffer.blit key 0ul key_p 0ul (Block.keylen prfa);
  State #i #rgn key_p (no_table i rgn)

// TODO leak, and eventually dynamic compromise.


(** computes a PRF block and copies its len first bytes to output *)

private val getBlock: 
  #i:id -> t:state i -> domain -> len:u32 {len <=^ blocklen} -> 
  output:lbuffer (v len) { Buffer.disjoint t.key output } -> ST unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 r h1 -> Buffer.live h1 output /\ Buffer.modifies_1 output h0 h1 ))
let getBlock #i t x len output =
  Buffer.recall t.key;
  Block.compute Block.CHACHA20 output t.key x.iv x.ctr len


// We encapsulate our 3 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table.
//
// For xor-based encryption,
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

// the first block (ctr=0) is used to generate a single-use MAC

val prf_mac: 
  i:id -> t:state i -> x:domain{x.ctr = 0ul} -> ST (MAC.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures (fun h0 mac h1 ->
    if prf i then
    ( let r = itable i t in
      match find_mac (HS.sel h0 r) x with // already in the table? 
      | Some mac' -> mac == mac' /\ h0 == h1 // when decrypting
      | None ->  // when encrypting, we get the stateful post of MAC.create             
        match find_mac (HS.sel h1 r) x with 
        | Some mac' -> mac == mac' /\ MAC.genPost0 (i,x.iv) t.rgn h0 mac h1
                      //16-10-11 we miss a more precise clause capturing the table update   
        | None -> False )
    else (
      HS.modifies (Set.singleton t.rgn) h0 h1 /\
      HS.modifies_ref t.rgn TSet.empty h0 h1 
  )))

#reset-options "--z3timeout 1000"

let prf_mac i t x =
  let macId = (i,x.iv) in
  if prf i then 
    begin
    let r = itable i t in 
    let contents = recall r; !r in 
    match find_mac contents x with
    | Some mac -> mac
    | None ->
      let mac = MAC.gen macId t.rgn in
      recall r; 
      r := SeqProperties.snoc contents (Entry x mac);
      mac
    end    
  else
    begin
    Buffer.recall t.key;
    let keyBuffer = Buffer.rcreate t.rgn 0uy keylen in
    let h1 = HST.get() in 
    getBlock t x keylen keyBuffer;
    let h2 = HST.get() in 
    Buffer.lemma_reveal_modifies_1 keyBuffer h1 h2;
    MAC.coerce macId t.rgn keyBuffer
    end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

(*
private let lemma_modifies_buf_1 (#t:Type) (b:Buffer.buffer t) (r:HH.rid{r <> Buffer.frameOf b}) h0 h1 :
  Lemma
    (requires (Buffer.live h0 b /\ HS.modifies (Set.singleton r) h0 h1))
    (ensures  (Buffer.modifies_buf_1 (Buffer.frameOf b) b h0 h1))
    = ()

private let lemma_modifies_ref (#t:Type) (r:HS.ref t) (rgn:HH.rid{rgn <> HS (r.id)}) h0 h1 :
  Lemma
    (requires (HS.modifies (Set.singleton (rgn)) h0 h1 /\ HS (rgn `is_in` h0.h /\ r.id `is_in` h0.h)))
    (ensures  (HS.modifies_ref (HS (r.id)) (TSet.singleton (FStar.Heap.Ref (HS.as_ref r))) h0 h1))
    = cut (HS.modifies (Set.union (Set.singleton rgn) (Set.singleton (HS (r.id)))) h0 h1);
      cut (HH.modifies_rref (HS (r.id)) !{} (HS (h0.h)) (HS (h1.h)))
*)

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
private val prf_raw: 
  i:id -> t:state i -> x:domain{x.ctr <> 0ul /\ ~(safeId i)} -> l:u32 {l <=^ blocklen} -> 
  output:lbuffer (v l) {Buffer.frameOf output <> t.rgn} -> ST unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 _ h1 -> modifies_x_buffer_1 t x output h0 h1)) 

let prf_raw i t x l output =
  if prf i then
    begin
    let r = itable i t in 
    let contents = recall r; !r in
    let h0 = HST.get() in
    let block = 
      match find_blk contents x with 
      | Some block -> block
      | None ->
          let block = random_bytes blocklen in
          r := SeqProperties.snoc contents (Entry x block);
          // assert(extends (HS.sel h0 r) (HS.sel h' r) x);
          block
    in
    let h1 = HST.get() in
    assert(extends (HS.sel h0 r) (HS.sel h1 r) x);
    store_bytes l output (Seq.slice block 0 (v l));
    let h2 = HST.get() in
    Buffer.lemma_reveal_modifies_1 output h1 h2
    //assert(HS.sel h1 r == HS.sel h2 r);
    //assert(extends (HS.sel h0 r) (HS.sel h2 r) x);
    //lemma_modifies_prf_raw r output h0 h1 h2)
    end
  else
    getBlock t x l output


// reuse the same block for x and XORs it with ciphertext
val prf_dexor: 
  i:id -> t:state i -> x:domain{x.ctr <> 0ul} -> l:u32 {l <=^ blocklen} -> 
  plain:plainBuffer i (v l) -> cipher:lbuffer (v l) 
  { Buffer.disjoint (as_buffer plain) cipher /\
    Buffer.frameOf (as_buffer plain) <> t.rgn } -> ST unit
  (requires (fun h0 ->
     Plain.live h0 plain /\ Buffer.live h0 cipher /\ 
     (safeId i ==>
     ( match find_otp (HS.sel h0 (itable i t)) x with
       | Some (OTP l' p c) -> l == l' /\ c == sel_bytes h0 l cipher
       | None -> False
     ))))
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

#reset-options "--z3timeout 30"

let prf_dexor i t x l plain cipher =
  if safeId i then
    let r = itable i t in 
    let contents = recall r; !r in
    match find_otp contents x with
    | Some (OTP l' p c) -> 
        let h0 = HST.get() in
        Plain.store #i l plain p;
        let h1 = HST.get() in
        Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0 h1
  else
    let h0 = HST.get() in
    let plainrepr = bufferRepr #i #(v l) plain in
    assert(Buffer.disjoint plainrepr cipher);
    prf_raw i t x l plainrepr; 
    let h1 = HST.get() in
    assert(modifies_x_buffer_1 t x plainrepr h0 h1);
    (if prf i then recall (itable i t));
    Buffer.Utils.xor_bytes_inplace plainrepr cipher l;
    let h2 = HST.get() in
    Buffer.lemma_reveal_modifies_1 plainrepr h1 h2;
    assert(prf i ==> HS.sel h1 (itable i t) == HS.sel h2 (itable i t));
    assert(modifies_x_buffer_1 t x plainrepr h0 h2)

#set-options "--initial_fuel 1 --max_fuel 1"

//TODO (NS): this one takes about 15s to prove automatically; investigate a bit
private let lemma_snoc_found (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) (v:range rgn i x) : Lemma
  (requires (find s x == None))
  (ensures (find (SeqProperties.snoc s (Entry x v)) x == Some v))
  = ()

#reset-options "--z3timeout 100"

// generates a fresh block for x and XORs it with plaintext
val prf_enxor: 
  i:id -> t:state i -> x:domain{x.ctr <> 0ul} -> l:u32 {l <=^ blocklen} -> 
  cipher:lbuffer (v l) -> plain:plainBuffer i (v l) 
  {  Buffer.disjoint (as_buffer plain) cipher /\ 
     Buffer.frameOf (as_buffer plain) <> t.rgn /\ 
     Buffer.frameOf cipher <> t.rgn } -> ST unit
  (requires (fun h0 ->
     Plain.live h0 plain /\ Buffer.live h0 cipher /\
     (safeId i ==> find_otp #t.rgn #i (HS.sel h0 t.table) x == None)))
  (ensures (fun h0 _ h1 ->
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     modifies_x_buffer_1 t x cipher h0 h1 /\
     (safeId i ==> 
       ( match find_otp #t.rgn #i (HS.sel h1 t.table) x with
         | Some (OTP l' p c) -> l = l' /\ p == sel_plain h1 l plain /\ c == sel_bytes h1 l cipher
         | None   -> False
     ))))
let prf_enxor i t x l cipher plain =
  if safeId i then
    let r = itable i t in 
    let contents = recall r; !r in 
    let p = Plain.load #i l plain in
    let c = random_bytes l in // sample a fresh ciphertext block
    let newblock = OTP #i l p c in
    let contents' = SeqProperties.snoc contents (Entry x newblock) in
    lemma_snoc_found contents x newblock;
    assert(find_otp #t.rgn #i contents x == None); 
    assert(find_otp #t.rgn #i contents' x == Some newblock);

    let h0 = HST.get() in
    assert(p == sel_plain h0 l plain);
    store_bytes l cipher c;
    let h1 = HST.get() in
    Buffer.lemma_reveal_modifies_1 cipher h0 h1;
    assert(p == sel_plain h1 l plain);
    r := contents';
    let h2 = HST.get() in
    assert(p == sel_plain h2 l plain); //16-10-12  how to anti-alias a buffer?
    assert(modifies_x_buffer_1 t x cipher h0 h2);
    ()
  else
    let h0 = HST.get() in 
    let plainrepr = bufferRepr #i #(v l) plain in
    assert(Buffer.disjoint plainrepr cipher);
    prf_raw i t x l cipher;
    let h1 = HST.get() in
    assert(modifies_x_buffer_1 t x cipher h0 h1);
    (if prf i then recall (itable i t));
    Buffer.Utils.xor_bytes_inplace cipher plainrepr l;
    let h2 = HST.get() in
    Buffer.lemma_reveal_modifies_1 cipher h1 h2;
    assert(prf i ==> HS.sel h1 (itable i t) == HS.sel h2 (itable i t));
    assert(modifies_x_buffer_1 t x cipher h0 h2)
