module Crypto.Symmetric.Chacha20.PRF

(* This file models our idealization of CHACHA20 (and soon any other
   block cipher used only in forward mode, such as AES for GCM or CCM)
   as a PRF to build authenticated encryption. 

   It models (an ad hoc variant of) the PRF security assumption:

   It captures the 3 different uses of the PRF in this construction:
   to generate the one-time MAC key, to generate a one-time-pad for
   encryption, and to generate a one-time-pad for decryption. *)

// TODO erase bookkeeping when ideal
// TODO add conditional idealization
// TODO improve agility (more i:id) and also support AES 
// TODO add pre- to statically prevent counter overflows

open FStar.HST
open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.HST.Monotonic.RRef

open Crypto.Symmetric.Bytes // including library stuff
open Plain

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC   = Crypto.Symmetric.Poly1305.MAC
module Block = Crypto.Symmetric.BlockCipher

let prfa = Block.CHACHA20

// LIBRARY STUFF 

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

// to be implemented from MAC.random
assume val random: l:u32 -> ST (lbytes (v l)) 
  (requires (fun m -> True))
  (ensures  (fun m0 _ m1 -> HS.modifies Set.empty m0 m1))
(*
let random len = 
  let buf = Buffer.create 0ul len in 
  MAC.random buf len; 
  load_bytes len buf
*)

type region = rgn:HH.rid {HS.is_eternal_region rgn}

// PRF TABLE 

let maxCtr = 2000ul // to be adjusted, controlling concrete bound. 
type ctrT = x:u32 {x <=^ maxCtr}  


// used only ideally; noeq is painful here. 

type domain = { iv:Block.iv prfa; ctr:ctrT } // could move to concrete CHACHA20
let incr (x:domain {x.ctr <^ maxCtr})  = { iv = x.iv; ctr = x.ctr +^ 1ul }

let blocklen = Block.blocklen prfa
let block = b:bytes {Seq.length b = v blocklen}

let keylen = Block.keylen prfa

// the range of our PRF, after idealization and "reverse inlining."
// for one-time-pads, we keep both the plain and cipher blocks, instead of their XOR.

type smac (rgn:region) i x = mac: MAC.state (i,x.iv) { MAC.State.region mac = rgn }
noeq type otp i = | OTP: l:u32 {l <=^ blocklen} -> plain i (v l) -> cipher:lbytes (v l) -> otp i

let range (rgn:region) (i:id) (x:domain): Type0 =
  if x.ctr = 0ul 
  then smac rgn i x 
  else otp i

// explicit coercions
let macRange rgn i (x:domain{x.ctr = 0ul}) (v:range rgn i x) : smac rgn i x = v
let otpRange rgn i (x:domain{x.ctr <> 0ul}) (v:range rgn i x) : otp i        = v
 
noeq type entry (rgn:region) (i:id) = | Entry: x:domain -> range:range rgn i x -> entry rgn i

let find (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) : option (range rgn i x) =
  match SeqProperties.seq_find (fun (e:entry rgn i) -> e.x = x) s with 
  | Some e -> Some e.range 
  | None   -> None

let find_0 #rgn #i s (x:domain{x.ctr=0ul}) = 
  match find s x with
  | Some v -> Some(macRange rgn i x v)
  | None   -> None

let find_1 #rgn #i s (x:domain{x.ctr<>0ul}) = 
  match find s x with
  | Some v -> Some(otpRange rgn i x v)
  | None   -> None

// the PRF instance, including its key and memoization table
// TODO separate on rw, with multiple readers? 
noeq type state (i:id) = 
  | State: #rgn: region ->
           // key is immutable once generated, we should rather use lbytes ...
           key:lbuffer (v (Block.keylen prfa)) {Buffer.frameOf key = rgn} -> 
           table:HS.ref (Seq.seq (entry rgn i)) {HS.frameOf table = rgn} -> 
           state i  // should be maybe_mrref; for later. 

// TODO coerce, leak, and eventually dynamic compromise.

val gen: rgn: region -> i:id -> ST (state i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> HS.sel h1 s.table == Seq.createEmpty #(entry rgn i)))

let gen rgn i =
  // SZ: let key = MAC.random rgn Block.keylen`?
  let key = Buffer.rcreate rgn 0uy (Block.keylen prfa) in
  store_bytes (Block.keylen prfa) key (random (Block.keylen prfa));
  let table = ralloc rgn (Seq.createEmpty #(entry rgn i)) in
  State #i #rgn key table

// computes a PRF block and copies its len first bytes to output

assume val buffer_recall: b:buffer {HS.is_eternal_region (Buffer.frameOf b)} -> Stack unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> h0 == h1 /\ Buffer.live h1 b))

private val getBlock: #i:id -> t:state i -> domain -> len:u32 {len <=^ blocklen} -> output:lbuffer (v len) -> ST unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 r h1 -> Buffer.live h1 output /\ Buffer.modifies_1 output h0 h1 ))
//TODO: we need some way to recall that t.key is in an eternal region and can be recalled
let getBlock #i t x len output = 
  buffer_recall t.key; 
  assume(Buffer.disjoint t.key output); //16-10-02 
  Block.compute Block.CHACHA20 output t.key x.iv x.ctr len


// We encapsulate our 3 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table. 
//
// For xor-based encryption, 
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

 
// the first block (ctr=0) is used to generate a single-use MAC
val prf_mac: i:id -> t:state i -> x:domain{x.ctr = 0ul} -> ST (MAC.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures (fun h0 mac h1 -> 
    authId i ==>
    ( match find_0 (HS.sel h1 t.table) x with 
      | Some mac' -> mac == mac' /\ MAC.genPost (i,x.iv) t.rgn h0 mac h1
      | None      -> False
    // we guarantee the stateful post of MAC.create when x is not in the table. 
    // in all cases, we return the state in the table
  )))

// reuse the same block for x and XORs it with ciphertext
val prf_dexor: i:id -> t:state i -> x:domain{x.ctr <> 0ul} -> 
  l:u32 {l <=^ blocklen} -> plain:plainBuffer i (v l) -> cipher:lbuffer (v l) -> ST unit
  (requires (fun h0 -> 
     Plain.live h0 plain /\ Buffer.live h0 cipher /\ Buffer.disjoint (bufferT plain) cipher /\ 
     Buffer.frameOf (bufferT plain) <> t.rgn /\
     (authId i ==> 
     ( match find_1 (HS.sel h0 t.table) x with 
       | Some (OTP l' p c) -> l == l' /\ c == sel_bytes h0 l cipher
       | None -> False
     ))))
  (ensures (fun h0 _ h1 -> 
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     Buffer.modifies_1 (bufferT plain) h0 h1 /\
     (authId i ==>
       ( match find_1 (HS.sel h1 t.table) x with 
         | Some (OTP l' p c) -> l == l' /\ p == sel_plain h1 l plain
         | None -> False 
     ))))
 
let prf_dexor i t x l plain cipher = 
  if authId i then
    begin
      recall t.table;
      let contents = !t.table in
      match find_1 contents x with 
      | Some (OTP l' p c) -> ( 
          let h0 = HST.get() in
          Plain.store #i l plain p;
          let h1 = HST.get() in 
          Buffer.lemma_reveal_modifies_1 (bufferT plain) h0 h1)
//          let contents' = !t.table in
//          assert(Buffer.frameOf (bufferT plain) <> t.rgn);
//          assert(contents == contents') 
    end
  else
    begin
      let plain = bufferRepr #i #(v l) plain in 
      getBlock t x l plain; 
      Buffer.Utils.xor_bytes_inplace plain cipher l
    end

//TODO (NS): this one takes about 15s to prove automatically; investigate a bit
let lemma_snoc_found (#rgn:region) (#i:id) (s:Seq.seq (entry rgn i)) (x:domain) (v:range rgn i x) : Lemma
  (requires (find s x == None))
  (ensures (find (SeqProperties.snoc s (Entry x v)) x == Some v))
  = ()  

#reset-options "--z3timeout 10000"
//SZ: Was this typechecking? No. CF: Yes, up to explicit assumptions.

// generates a fresh block for x and XORs it with plaintext
val prf_enxor: i:id -> t:state i -> x:domain{x.ctr <> 0ul} -> 
  l:u32 {l <=^ blocklen} -> cipher:lbuffer (v l) -> plain:plainBuffer i (v l) -> ST unit
  (requires (fun h0 -> 
     Buffer.frameOf cipher <> t.rgn /\
     Plain.live h0 plain /\ Buffer.live h0 cipher /\ 
     Buffer.disjoint (bufferT plain) cipher /\
     is_None(find_1 (HS.sel h0 t.table) x) 
     ))
  (ensures (fun h0 _ h1 -> 
     Plain.live h1 plain /\ Buffer.live h1 cipher /\
     Buffer.modifies_1 cipher h0 h1 /\ //16-09-22 missing hybrid modifies also covering t.
     (authId i ==> 
       ( match find_1 (HS.sel h1 t.table) x with 
         | Some (OTP l' p c) -> l = l' /\ p == sel_plain h1 l plain /\ c == sel_bytes h1 l cipher
         | None   -> False 
     ))))
let prf_enxor i t x l cipher plain = 
  if authId i then
    begin
      recall t.table;
      let p = Plain.load #i l plain in
      let c = random l in // sample a fresh ciphertext block    
      store_bytes l cipher c;  //NS: this write to cipher may disturb the contents of t.table; need an anti-aliasing assumption there
      assume false;//16-10-02 
      let contents = !t.table in //NS: Or, we can move this read up; but the anti-aliasing seems like the right thing to do
      let newblock = OTP #i l p c in
      assert(find contents x == None); //TODO how to avoid explicit annotations on find_1 ? NS: find_1 is fine here; without the store_bytes this assertion succeeds
      lemma_snoc_found contents x newblock; 
      t.table := SeqProperties.snoc contents (Entry x newblock) //NS: t.table is mutated;  so the modifies_1 cipher h0 h1 cannot be true
    end
  else
    begin
      let plain = bufferRepr #i #(v l) plain in
      getBlock t x l cipher;
      Buffer.Utils.xor_bytes_inplace cipher plain l
    end

let prf_mac i t x = 
  if authId i then 
    begin
      assume false; //16-10-02 
      recall t.table;
      let contents = !t.table in //TODO unclear which pre is missing
      match find_0 contents x with 
      | Some mac -> mac 
      | None     ->
        begin
          let mac = MAC.gen (i,x.iv) t.rgn in
          t.table := SeqProperties.snoc contents (Entry x mac);
          mac
        end
    end
  else
    begin
      let keyBytes = Buffer.rcreate t.rgn 0uy keylen in
      getBlock t x keylen keyBytes;
      let macId = (i,x.iv) in
      MAC.coerce macId t.rgn keyBytes
    end
