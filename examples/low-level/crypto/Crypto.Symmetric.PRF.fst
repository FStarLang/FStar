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
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Flag
open Crypto.Plain
open FStar.HyperStack.ST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module MAC   = Crypto.Symmetric.MAC
module CMA   = Crypto.Symmetric.UF1CMA
module Block = Crypto.Symmetric.Cipher

// PRF TABLE

let blocklen i = Block.blocklen (cipherAlg_of_id i)
type block i = b:lbytes (v (blocklen i))
let keylen i = Block.keylen (cipherAlg_of_id i)
let statelen i = Block.statelen (cipherAlg_of_id i)

(*
private let lemma_lengths (i:id) : Lemma(keylen i <^ blocklen i) =
  match i.cipher with
  | AES_256_GCM -> ()
  | CHACHA20_POLY1305 -> ()
*)

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

type domain (i:id) = { iv:Block.iv (cipherAlg_of_id i); ctr:ctrT i}
let incr (i:id) (x:domain i {x.ctr <^ maxCtr i}) = { iv = x.iv; ctr = x.ctr +^ 1ul }

val above: #i:id -> domain i -> domain i -> GTot bool
let above #i x z = x.iv = z.iv && x.ctr >=^ z.ctr

// the range of our PRF, after idealization and "reverse inlining."
// for one-time-pads, we keep both the plain and cipher blocks, instead of their XOR.

type smac (rgn:region) (i:id) x = mac: CMA.state (i,x.iv) { CMA.State?.region mac = rgn }
noeq type otp (i:id) = | OTP: l:u32 {l <=^ blocklen i} -> plain i (v l) -> cipher:lbytes (v l) -> otp i

let ctr_0 (i:id) = if CMA.skeyed i then 1ul else 0ul
let range (mac_rgn:region) (i:id) (x:domain i): Type0 =
  if      x.ctr <^ ctr_0 i then CMA.skey mac_rgn i
  else if x.ctr  = ctr_0 i then smac mac_rgn i x
  else if safeId i        then otp i
                          else lbytes (v (blocklen i))

inline_for_extraction let iv_0 () = FStar.UInt128.uint64_to_uint128 0UL
noextract let domain_sk0 (i:id) = x:domain i{x.ctr <^ ctr_0 i /\ x.iv = iv_0 () }
noextract let domain_mac (i:id) = x:domain i{x.ctr = ctr_0 i}
noextract let domain_otp (i:id) = x:domain i{x.ctr >^ ctr_0 i /\ safeId i}
noextract let domain_blk (i:id) = x:domain i{x.ctr >^ ctr_0 i /\ ~ (safeId i)}

// explicit coercions
noextract let sk0Range rgn (i:id) (x:domain_sk0 i) (z:range rgn i x) : CMA.skey rgn i = z
noextract let macRange rgn (i:id) (x:domain_mac i) (z:range rgn i x) : smac rgn i x = z
noextract let otpRange rgn (i:id) (x:domain_otp i) (z:range rgn i x) : otp i = z
noextract let blkRange rgn (i:id) (x:domain_blk i) (z:range rgn i x) : block i = z

noeq type entry (rgn:region) (i:id) =
  | Entry: x:domain i -> range:range rgn i x -> entry rgn i
type table (rgn:region) (i:id) = Seq.seq (entry rgn i)

// Doesn't extract because: polymorphic comparison
noextract let is_entry_domain (#i:id) (#rgn:rid) (x:domain i) (e:entry rgn i) : Tot bool = e.x = x

noextract let find (#rgn:region) (#i:id) (s:table rgn i) (x:domain i) : option (range rgn i x) =
  match Seq.find_l (is_entry_domain x) s with
  | Some e -> Some e.range
  | None   -> None

let find_sk0 #rgn (#i:id) s (x:domain_sk0 i) =
  match find s x with
  | Some v -> Some(sk0Range rgn i x v)
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

(* not sure why it fails; inlined below.
#reset-options "--z3rlimit 100"
private val lemma_find_snoc: #rgn:region -> #i:id -> s:table rgn i -> e:entry rgn i -> Lemma (ensures (find (Seq.snoc s e) e.x == Some e.range))
let lemma_find_snoc #rgn #i s e =
  Seq.find_snoc s e (is_entry_domain e.x)
*)


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
           key: lbuffer (v (statelen i))
             {Buffer.frameOf key = rgn /\ ~(HS.is_mm (Buffer.content key))} ->
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
    (prf i ==>
        ~ (h0 `HS.contains` (itable i s))
    /\ HS.sel h1 (itable i s) == Seq.empty #(entry s.mac_rgn i))))
let gen rgn i =
  push_frame();
  let mac_rgn : (r:region{r `HH.extends` rgn}) = new_region rgn in
  let keystate = Buffer.rcreate rgn 0uy (statelen i) in
  let key = Buffer.create 0uy (keylen i) in
  let alg = cipherAlg_of_id i in
  Bytes.random (v (keylen i)) key;
  Block.init #i key keystate;
  let table: table_t rgn mac_rgn i =
    if prf i then
      mktable i rgn mac_rgn (ralloc rgn (Seq.empty #(entry mac_rgn i)))
    else ()
  in
  pop_frame();
  State #i #rgn #mac_rgn keystate table
// no need to demand prf i so far.

val coerce: rgn:region -> i:id{~(prf i)} -> key:lbuffer (v (keylen i)) -> ST (state i)
  (requires (fun h -> Buffer.live h key))
  (ensures  (fun h0 s h1 -> s.rgn == rgn))
let coerce rgn i key =
  let mac_rgn : (r:region{r `HH.extends` rgn}) = new_region rgn in
  let keystate = Buffer.rcreate rgn 0uy (statelen i) in
  let alg = cipherAlg_of_id i in
  Cipher.init #i key keystate;
  State #i #rgn #mac_rgn keystate (no_table i rgn mac_rgn)

val leak: #i:id{~(prf i)} -> st:state i -> ST (key:lbuffer (v (statelen i)))
  (requires (fun h -> True))
  (ensures  (fun h0 k h1 -> h0==h1 /\ Buffer.live h1 k))
let leak #i st =
  Buffer.recall st.key;
  st.key

(** computes a PRF block and copies its len first bytes to output *)

// JP: removing the private since this function is called by test-perf.exe
val getBlock:
  #i:id -> t:state i -> domain i -> len:u32 {len <=^ blocklen i} ->
  output:lbuffer (v len) { Buffer.disjoint t.key output } -> STL unit
  (requires (fun h0 -> Buffer.live h0 output))
  (ensures (fun h0 r h1 -> Buffer.live h1 output /\ Buffer.modifies_1 output h0 h1 ))
let getBlock #i t x len output =
  Buffer.recall t.key;
  Block.compute i output t.key x.iv x.ctr len


// We encapsulate our 4 usages of the PRF in specific functions.
// But we still use a single, ctr-dependent range in the table.
//
// For xor-based encryption,
// the ideal variant records both the plaintext and the ciphertext
// whereas the real PRF output is their xor.

// the first block (ctr=0) is used to generate a single-use MAC

val prf_mac:
  i:id -> t:state i -> k_0: CMA.akey t.mac_rgn i -> x:domain_mac i -> ST (CMA.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures (fun h0 mc h1 -> (* beware: mac shadowed by CMA.mac *)
    if prf i then
      let r = itable i t in
      let t0 = HS.sel h0 r in
      let t1 = HS.sel h1 r in
      //16-12-20 now proved in AEAD: (forall (y:domain i). y <> x ==> find t0 y == find t1 y)  /\ //at most modifies t at x
      (match find_mac (HS.sel h0 r) x with // already in the table?
       | Some mc' ->
           h0 == h1 /\ // when decrypting
           mc == mc' /\
           CMA.(MAC.norm h1 mc.r) /\
           CMA.(Buffer.live h1 mc.s) /\
           CMA.(mac_log ==> m_contains (ilog mc.log) h1)
       | None ->  // when encrypting, we get the stateful post of MAC.create
         (match find_mac (HS.sel h1 r) x with
          | Some mc' ->
              mc == mc' /\
              t1 == Seq.snoc t0 (Entry x mc) /\
              CMA.genPost (i,x.iv) t.mac_rgn h0 mc h1 /\
              HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\
              HS.modifies_ref t.rgn (Set.singleton (Heap.addr_of (HS.as_ref r))) h0 h1 /\
   HS.modifies_ref t.mac_rgn Set.empty h0 h1
          | None -> False ))
    else (
      CMA.genPost (i,x.iv) t.mac_rgn h0 mc h1 /\
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\ //allocates in t.rgn and t.mac_rgn
      HS.modifies_ref t.rgn Set.empty h0 h1  /\              //but modifies nothing in them
      HS.modifies_ref t.mac_rgn Set.empty h0 h1 )))


#reset-options "--z3rlimit 100"

let prf_mac i t k_0 x =
  Buffer.recall t.key;
  recall_region t.mac_rgn;
  if CMA.skeyed i then Buffer.recall (CMA.get_skey #t.mac_rgn #i k_0);
  let macId = (i,x.iv) in
  if prf i then
    begin
    let r = itable i t in
    recall r;
    let contents = !r in
    match find_mac contents x with
    | Some mc ->  (* beware: mac shadowed by CMA.mac *)
        let h0 = ST.get() in
        assume (CMA.(MAC.norm h0 mc.r)); //16-12-20 TODO: replace this using monotonicity; NS: known limitation
        Buffer.recall (CMA.(mc.s));
        if mac_log then FStar.Monotonic.RRef.m_recall (CMA.(ilog mc.log));
        mc
    | None ->
        let mc = CMA.gen t.mac_rgn macId k_0 in
        r := Seq.snoc contents (Entry x mc);
        Seq.find_snoc contents (Entry x mc) (is_entry_domain x);
        mc
    end
  else
    let keyBuffer = Buffer.rcreate t.mac_rgn 0uy (CMA.keylen i) in
    let h1 = ST.get() in
    getBlock t x (CMA.keylen i) keyBuffer;
    let mc = CMA.coerce t.mac_rgn macId k_0 keyBuffer in
    let h3 = ST.get() in
    Buffer.lemma_reveal_modifies_1 keyBuffer h1 h3;
    mc


val prf_sk0:
  #i:id{ CMA.skeyed i } -> t:state i -> ST (CMA.skey t.mac_rgn i)
  (requires (fun h0 -> True))
  (ensures (fun h0 k h1 ->
    let x = { ctr=0ul; iv=iv_0() } in
    if prf i then
      let r = itable i t in
      let t0 = HS.sel h0 r in
      let t1 = HS.sel h1 r in
      //now proved in AEAD: (forall (y:domain i). y <> x ==> find t0 y == find t1 y)  /\ //at most modifies t at x
      Buffer.live h1 k /\
      (match find_sk0 #t.mac_rgn #i (HS.sel h0 r) x with // already in the table?
       | Some r0 -> k == r0 /\ h0 == h1
       | None ->
         (match find_sk0 (HS.sel h1 r) x with
          | Some r1 ->
              k == r1 /\
              t1 == Seq.snoc t0 (Entry x r1) /\
              HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\
              HS.modifies_ref t.rgn (Set.singleton (Heap.addr_of (HS.as_ref r))) h0 h1 /\
              HS.modifies_ref t.mac_rgn Set.empty h0 h1
          | None -> False ))
    else (
      Buffer.live h1 k /\
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\ //allocates in t.rgn
      HS.modifies_ref t.rgn Set.empty h0 h1  /\              //but nothing within it is modified
      HS.modifies_ref t.mac_rgn Set.empty h0 h1 )))

let prf_sk0 #i t =
  let x = { ctr=0ul; iv=iv_0() } in
  if prf i then
    begin
      let r = itable i t in
      recall r;
      let contents = !r in
      let sk0 = match find_sk0 contents x with
      | Some sk0 -> sk0
      | None ->
          let sk0 = CMA.get_skey (CMA.akey_gen t.mac_rgn i) in
          r := Seq.snoc contents (Entry x sk0);
          Seq.find_snoc contents (Entry x sk0) (is_entry_domain x);
          sk0 in
      Buffer.recall sk0;
      sk0
    end
  else
    let keyBuffer = Buffer.rcreate t.mac_rgn 0uy (CMA.skeylen i) in
    let h1 = ST.get() in
    getBlock t x (CMA.skeylen i) keyBuffer;
    let h2 = ST.get() in
    Buffer.lemma_reveal_modifies_1 keyBuffer h1 h2;
    keyBuffer


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let extends (#rgn:region) (#i:id) (s0:Seq.seq (entry rgn i))
      (s1:Seq.seq (entry rgn i)) (x:domain i{ctr_0 i <^ x.ctr}) =
  let open FStar.Seq in
  match find s0 x with
  | Some _ -> s0 == s1
  | None   -> Seq.length s1 = Seq.length s0 + 1 /\
       (Seq.index s1 (Seq.length s0)).x = x /\
       Seq.equal (Seq.slice s1 0 (Seq.length s0)) s0

// modifies a table (at most at x) and a buffer.
let modifies_x_buffer_1 #i (t:state i) x b h0 h1 =
  Buffer.live h1 b /\
  (if prf i then
    let r = itable i t in
    let rb = Buffer.frameOf b in
    // can't use !{ t.rgn, rb}, why?
    let rgns = Set.union (Set.singleton #HH.rid t.rgn) (Set.singleton #HH.rid rb) in
    HS.modifies rgns h0 h1 /\
    HS.modifies_ref t.rgn (Set.singleton (Heap.addr_of (HS.as_ref r))) h0 h1 /\
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

#reset-options "--z3rlimit 100"

let zero = 0

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
          r := Seq.snoc contents (Entry x block);
          // assert(extends (HS.sel h0 r) (HS.sel h' r) x);
          block
    in
    let h1 = ST.get() in
    assert(extends (HS.sel h0 r) (HS.sel h1 r) x);
    store_bytes len output (Seq.slice block zero (v len));
    let h2 = ST.get() in
    Buffer.lemma_reveal_modifies_1 output h1 h2
    end
  else
    getBlock t x len output

////////////////////////////////////////////////////////////////////////////////
//prf_dexor
////////////////////////////////////////////////////////////////////////////////
// reuse the same block for x and XORs it with ciphertext
let prf_dexor_modifies (#i:id) (#len:u32) (t:state i) (x:domain i{ctr_0 i <^ x.ctr})
             (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   if not (prf i) || safeId i
   then Buffer.modifies_1 (as_buffer pb) h0 h1
   else modifies_x_buffer_1 t x (as_buffer pb) h0 h1

let contains_cipher_block  (#i:id) (#r:rid) (l:nat)
         (x:domain i{safeId i /\ ctr_0 i <^ x.ctr})
         (cipher:lbytes l)
         (blocks:Seq.seq (entry r i))
  = match find_otp blocks x with
    | Some (OTP l' p c) -> l == v l' /\ c ==  cipher
    | None -> False

let prf_dexor_requires (i:id) (t:state i) (x:domain i{ctr_0 i <^ x.ctr})
            (l:u32 {l <=^ blocklen i})
                (cipher:lbuffer (v l))
            (plain:plainBuffer i (v l))
            (h0:mem) =
   Buffer.disjoint (as_buffer plain) cipher /\
   Buffer.frameOf (as_buffer plain) <> t.rgn /\
   Buffer.frameOf cipher <> t.rgn /\
   Crypto.Plain.live h0 plain /\
   Buffer.live h0 cipher /\
   (safeId i ==> contains_cipher_block (v l) x (Buffer.as_seq h0 cipher) (HS.sel h0 (itable i t)))

let contains_plain_block   (#i:id) (#r:rid) (#l:nat)
         (x:domain i{safeId i /\ ctr_0 i <^ x.ctr})
         (plain:plain i l)
         (blocks:Seq.seq (entry r i))
  = match find_otp blocks x with
    | Some (OTP l' p c) -> l == v l' /\ p == plain
    | None -> False

let prf_dexor_ensures (i:id) (t:state i) (x:domain i{ctr_0 i <^ x.ctr})
          (l:u32 {l <=^ blocklen i})
              (cipher:lbuffer (v l))
          (plain:plainBuffer i (v l))
          (h0:mem) (h1:mem) =
   let pb = as_buffer plain in
   Crypto.Plain.live h1 plain /\
   Buffer.live h1 cipher /\
   prf_dexor_modifies t x plain h0 h1 /\
   (safeId i ==> contains_plain_block x (sel_plain h1 l plain) (HS.sel h1 (itable i t)))

val prf_dexor:
  i:id -> t:state i -> x:domain i{ctr_0 i <^ x.ctr} -> l:u32 {l <=^ blocklen i} ->
  cipher:lbuffer (v l) -> plain:plainBuffer i (v l) -> ST unit
  (requires (fun h0 -> prf_dexor_requires i t x l cipher plain h0))
  (ensures (fun h0 _ h1 -> prf_dexor_ensures i t x l cipher plain h0 h1))
let prf_dexor i t x l cipher plain =
  if safeId i then
    let r = itable i t in
    let contents = recall r; !r in
    match find_otp contents x with
    | Some (OTP l' p c) ->
        let h0 = ST.get() in
        Crypto.Plain.store #i l plain p;
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
////////////////////////////////////////////////////////////////////////////////
//end: prf_dexor
////////////////////////////////////////////////////////////////////////////////


#reset-options "--z3rlimit 100"

// generates a fresh block for x and XORs it with plaintext
val prf_enxor:
  i:id -> t:state i -> x:domain i{ctr_0 i <^ x.ctr} -> l:u32 {l <=^ blocklen i} ->
  cipher:lbuffer (v l) -> plain:plainBuffer i (v l)
  {  Buffer.disjoint (as_buffer plain) cipher /\
     Buffer.frameOf (as_buffer plain) <> t.rgn /\
     Buffer.frameOf cipher <> t.rgn } -> ST unit
  (requires (fun h0 ->
     Crypto.Plain.live h0 plain /\
     Buffer.live h0 cipher /\
     (safeId i ==> find_otp #t.mac_rgn #i (HS.sel h0 (itable i t)) x == None)))
  (ensures (fun h0 _ h1 ->
     Crypto.Plain.live h1 plain /\ Buffer.live h1 cipher /\
     modifies_x_buffer_1 t x cipher h0 h1 /\
     (safeId i ==>  (
       let blocks = HS.sel h1 (itable i t) in
       contains_plain_block x (sel_plain h1 l plain) blocks /\
       contains_cipher_block (v l) x (sel_bytes h1 l cipher) blocks))))

       (* ( match find_otp #t.mac_rgn #i (HS.sel h1 t.table) x with *)
       (*   | Some (OTP l' p c) -> l = l' /\ p == sel_plain h1 l plain /\ c == sel_bytes h1 l cipher *)
       (*   | None   -> False )))) *)
let prf_enxor i t x l cipher plain =
  if safeId i then
    let r = itable i t in
    let contents = recall r; !r in
    let p = Crypto.Plain.load #i l plain in
    let c = random_bytes l in // sample a fresh ciphertext block
    let newblock = OTP #i l p c in
    let contents' = Seq.snoc contents (Entry x newblock) in
    Seq.find_snoc contents (Entry x newblock) (is_entry_domain x);

    let h0 = ST.get() in
    assert(p == sel_plain h0 l plain);
    store_bytes l cipher c;
    let h1 = ST.get() in
    Buffer.lemma_reveal_modifies_1 cipher h0 h1;
    assert(p == sel_plain h1 l plain);
    r := contents';
    let h2 = ST.get() in
    assert(p == sel_plain h2 l plain);
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
