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
module EtM.CPA
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open EtM.Ideal

open Platform.Bytes
module CC = EtM.CoreCrypto
module B = Platform.Bytes

open EtM.Plain

type rid = erid

(*** Basic types ***)

/// Initialization vectors: bytes of a given size
let ivsize = CC.blockSize CC.AES_128_CBC
let iv = lbytes ivsize

/// Raw keys for AES 128
let keysize = 16
let aes_key = lbytes keysize

/// Cipher-texts are a concatenation of the IV and the AES cipher
///    -- we underspecify its length
///    -- MK says: minimal cipher length twice blocksize?
let cipher = (b:bytes{B.length b >= ivsize})

(*** Ideal state ***)

/// CPA log entries are pairs of a plain text and its corresponding cipher
type log_entry =
  | Entry: plain:plain
         -> c:cipher
         -> log_entry

/// Recover the IV from an entry by splitting out a prefix of the cipher
let iv_of_entry (Entry _ c) : iv = fst (B.split c ivsize)

/// Recover the AES cipher from an entry by splitting out a suffix of the cipher
let raw_cipher (Entry _ c) : bytes = snd (B.split c ivsize)

/// A lemma inverting the iv+cipher construction
let split_entry (p:plain) (c:cipher) (iv:iv) (r:bytes)
   : Lemma  (iv_of_entry (Entry p (iv@|r)) == iv /\
             raw_cipher  (Entry p (iv@|r)) == r)
   = assert (Seq.equal (iv_of_entry (Entry p (iv@|r))) iv);
     assert (Seq.equal (raw_cipher (Entry p (iv@|r))) r)

/// A lemma showing that entries that differ on their IVs differ on their ciphers
///    -- because append is injective on both its arguments
let iv_of_entry_inj (e1 e2:log_entry)
  : Lemma (iv_of_entry e1 <> iv_of_entry e2 
           ==> Entry?.c e1 <> Entry?.c e2)
  = let iv1, r1 = iv_of_entry e1, raw_cipher e1 in
    let iv2, r2 = iv_of_entry e2, raw_cipher e2 in
    FStar.Classical.move_requires (Platform.Bytes.lemma_append_inj iv1 r1 iv2) r2

/// A key includes the raw AES key but also an monotonic log of entries
/// representing the ideal state
noeq 
type key =
  | Key: #region:rid 
       -> raw:aes_key 
       -> log:Monotonic.Seq.log_t region log_entry
       -> key

(** Exercise: (conceptually easy; technically difficult)

      The type `key` above contains a reference to an ideal log
      unconditionally.  However, this log is redundant when not
      idealizing.  Revise the `key` type as shown below and propagate
      it through the development.

      noeq 
      type key =
      | Key: #region:rid 
          -> raw:aes_key 
          -> log:(if Ideal.ind_cpa then Monotonic.Seq.log_t region log_entry else unit)
          -> key
 **)

/// An accessor for the log in state h
let log (k:key) (h:mem) 
  : GTot (seq log_entry) =
    sel h (Key?.log k)

(*** Invariants on the ideal state ***)

(** Informally, there are two main components to the invariant:

      1. The IVs in the log are pairwise-distinct. 
         We rely on this to obtain an injectivity property in EtM.AE,
         using it to relate the CPA and MAC logs to the composite AE log.
         
      2. The ciphers in each entry are required to be valid encryptions of
         the corresponding plain texts and IVs
 **)

/// ---------------------------------------
/// Invariant part 1: distinctness of IVs
/// ---------------------------------------

let iv_not_in (iv:iv) (log:seq log_entry) =
    forall (e:log_entry{Seq.mem e log}). iv_of_entry e <> iv

/// We state pairwise-distinctness of IVs in this recursive form
/// It makes it more convenient to work with as we
/// append each new entry (aka snoc) to the end of the log
let rec pairwise_distinct_ivs (log:seq log_entry) 
  : Tot Type0 (decreases (Seq.length log)) =
  if Seq.length log > 0 then
    let log, tl = Seq.un_snoc log in
    pairwise_distinct_ivs log /\
    iv_not_in (iv_of_entry tl) log
  else True

/// A simple lemma to introduce and eliminate pairwise_distinct_ivs
let pairwise_snoc (cpas:Seq.seq log_entry) (tl:log_entry)
    : Lemma ((pairwise_distinct_ivs cpas /\ iv_not_in (iv_of_entry tl) cpas) <==>
             (pairwise_distinct_ivs (Seq.snoc cpas tl)))
    = un_snoc_snoc cpas tl

/// It's convenient to lift the pairwise-distinctness of IVs to
/// pairwise distinctness of the cipher texts
let invert_pairwise (cpas:Seq.seq log_entry) (e:log_entry) (c:cipher)
    : Lemma (requires (pairwise_distinct_ivs (snoc cpas e) /\
                       Entry?.c e == c))
            (ensures (forall e'. Seq.mem e' cpas ==> Entry?.c e' <> c))
    = pairwise_snoc cpas e;
      FStar.Classical.forall_intro (iv_of_entry_inj e)

/// -----------------------------------------
/// Invariant part 2: correctness of ciphers
/// -----------------------------------------

/// Each entry contains a valid AES encryption
/// 
///   -- A wrinkle is that when ind_cpa, rather than encrypting the
///      plaintext we just encrypt zeros
let entry_functional_correctness (raw_key:bytes) (e:log_entry) : Type0 =
    let iv = iv_of_entry e in
    let c = raw_cipher e in
    let plain = Entry?.plain e in
    let p = if ind_cpa then createBytes (length plain) 0z else repr plain in
     c == CC.block_encrypt_spec CC.AES_128_CBC raw_key iv p

/// Lifting the correctness of individual entries pointwise to correctness of the entire log
let cipher_functional_correctness (raw_key:bytes) (log:seq log_entry) =
    forall (e:log_entry{Seq.mem e log}). {:pattern (Seq.mem e log)}
      entry_functional_correctness raw_key e

/// The invariant is the conjunction of distinctness and correctness
///   -- Together with a technical requirement of the log actually
///      being present in the memory
let invariant (k:key) (h:mem) =
    let Key raw_key lg = k in
    let log = log k h in
    contains h lg /\ //<-- technical: the log must be allocated
    pairwise_distinct_ivs log /\
    cipher_functional_correctness raw_key log


(*** The main interface:
       keygen, encrypt, decrypt  ***)
/// keygen: allocating a new key
///       -- Caller provides a parent region in which to allocate the ideal log
///       -- Returns a fresh key satisfying its invariant whose log is initially empty
let keygen (parent:rid)
  : ST key
  (requires (fun _ -> HyperStack.ST.witnessed (region_contains_pred parent)))
  (ensures  (fun m0 k m1 -> 
               modifies Set.empty m0 m1    /\
               extends k.region parent  /\
               fresh_region k.region m0 m1 /\
               log k m1 == Seq.empty /\
               invariant k m1)) =
  let raw = CC.random keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region Seq.empty in
  Key #region raw log

/// A primitive to sample a fresh iv distinct from others
///    Exercise: Implement this, e.g, by simply incrementing a counter
///              Or by sampling and retrying
assume 
val fresh_iv (k:key) : ST iv
    (requires (fun h -> True))
    (ensures (fun h0 iv h1 -> 
                h0 == h1 /\
                iv_not_in iv (log k h0)))


/// encrypt:
///     -- requires a key initially in the invariant
///     -- ensures that only the key's region is modifie
///        and that the the key's log grows by just one entry
let encrypt (k:key) (m:plain)
  : ST cipher
  (requires (invariant k))
  (ensures  (fun h0 c h1 ->
    (let log0 = log k h0 in
     let log1 = log k h1 in
     invariant k h1 /\
     modifies_one k.region h0 h1 /\
     contains h1 k.log  /\
     log1 == snoc log0 (Entry m c)))) =
  let iv = fresh_iv k in
  let text = if ind_cpa
             then createBytes (length m) 0z
             else repr m in
  let raw_c = CC.block_enc CC.AES_128_CBC k.raw iv text in
  let c = iv@|raw_c in
  let e = Entry m c in
  split_entry m c iv raw_c;
  assert (entry_functional_correctness k.raw e);
  let h0 = FStar.HyperStack.ST.get () in  
  write_at_end k.log e;
  let h1 = FStar.HyperStack.ST.get () in
  lemma_mem_snoc (log k h0) e;
  pairwise_snoc (log k h0) e;
  c

/// find_entry: An auxiliary function with a somewhhat technical proof
///    -- We search for an entry in a log that contains a cipher using
///       a left-to-right scan of the sequence provide by Seq.seq_find
///    -- Knowing that a the cipher exists in the log (via Seq.mem)
///       guarantees that this scan will succeed.
let find_entry (log:seq log_entry) (c:cipher) : Pure log_entry
    (requires (exists p. Seq.mem (Entry p c) log))
    (ensures (fun e -> Seq.mem e log /\ Entry?.c e == c))
  = let entry_has_cipher (c:cipher) (e:log_entry) = Entry?.c e = c in
    let eopt = Seq.seq_find (entry_has_cipher c) log in
    FStar.Classical.exists_elim
             (Some? eopt /\ Seq.mem (Some?.v eopt) log /\ entry_has_cipher c (Some?.v eopt))
             ()
             (fun (p:plain{Seq.mem (Entry p c) log}) -> 
                Seq.find_mem log (entry_has_cipher c) (Entry p c));
    Some?.v eopt                

/// decrypt:
///    -- An important pre-condition of decrypt is that when idealizing
///       (ind_cpa_rest_adv), we need to know that the cipher being decrypted
///       is actually the valid encryption of some plain text already in the log.
///
///    -- This allow us to prove that the plain text returned is a
///       valid decryption
let decrypt (k:key) (c:cipher)
  : ST plain
  (requires (fun h0 ->
    let log = log k h0 in
    invariant k h0 /\
    (b2t ind_cpa_rest_adv ==> (exists p. Seq.mem (Entry p c) log))))
  (ensures  (fun h0 res h1 ->
    let log = log k h1 in
    modifies_none h0 h1 /\
    invariant k h1 /\
    (b2t ind_cpa_rest_adv ==> Seq.mem (Entry res c) log))) =
  let Key raw_key log = k in
  let iv,c' = split c ivsize in
  let raw_plain = CC.block_dec CC.AES_128_CBC raw_key iv c' in
  if ind_cpa_rest_adv then
    let log = !log in
    let Entry plain _ = find_entry log c in
    split_entry plain c iv c';
    if not ind_cpa then begin
       //no correction necessary: raw_plain is the corrext plain text already
       CC.enc_dec_inverses CC.AES_128_CBC raw_key iv (repr plain);
       assert (repr plain == raw_plain);
       plain
    end
    else begin
      let zeroes = createBytes (length plain) 0z in
      CC.enc_dec_inverses CC.AES_128_CBC raw_key iv zeroes;
      assert (raw_plain == zeroes);
      plain
    end
  else coerce raw_plain
