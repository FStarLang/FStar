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
module OPLSS.AE
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

module MAC = OPLSS.MAC
module CPA = OPLSS.CPA
module Ideal = OPLSS.Ideal
module Plain = OPLSS.Plain
module B = LowStar.Monotonic.Buffer

(*** Basic types ***)


/// An AE key pairs an encryption key, ke, with a MAC'ing key, km,
/// with an invariant ensuring that their memory footprints of their
/// ideal state are disjoint.
/// 
/// Aside from this, we have an AE log, which is a view of the two
/// other logs.
noeq type key =
  | Key: mac:MAC.key
       -> enc:CPA.key { 
           B.loc_disjoint (B.loc_mreference mac.MAC.log)
                          (B.loc_mreference enc.CPA.log)
           }
       -> key

/// mac log
let mac_log (h:mem) (k:key) =
  sel h k.mac.MAC.log

/// cpa log
let cpa_log (h:mem) (k:key) =
  sel h k.enc.CPA.log

(*** Main invariant on the ideal state ***)
(** There are two main components to this invariant

     1. mac_only_cpa_ciphers: 
       
        The MAC log and CPA logs are related, in that the MAC log only
        contains entries for valid ciphers recorded the CPA log

     2. The CPA invariant (pairwise distinctness of IVs, notably)
**)

let mac_cpa_related (mac:MAC.log_entry) (enc:CPA.log_entry) =
  mac.MAC.msg == enc.CPA.c

/// See the comment above, for part 2 of the invariant
///   -- As in EtM.CPA, we state the invariant recursively
///      matching entries up pointwise
let rec mac_only_cpa_ciphers (macs:Seq.seq MAC.log_entry) 
                             (cpas:Seq.seq CPA.log_entry)
      : Tot Type0 (decreases (Seq.length macs)) =
   Seq.length macs == Seq.length cpas /\
   (if Seq.length macs > 0 then
     let macs, mac = Seq.un_snoc macs in
     let cpas, cpa = Seq.un_snoc cpas in
     mac_cpa_related mac cpa /\
     mac_only_cpa_ciphers macs cpas
    else True)

/// A lemma to intro/elim the recursive predicate above
let mac_only_cpa_ciphers_snoc (macs:Seq.seq MAC.log_entry) (mac:MAC.log_entry)
                              (cpas:Seq.seq CPA.log_entry) (cpa:CPA.log_entry)
  : Lemma (mac_only_cpa_ciphers (snoc macs mac) (snoc cpas cpa) <==>
          (mac_only_cpa_ciphers macs cpas /\ mac_cpa_related mac cpa))
  = un_snoc_snoc macs mac;
    un_snoc_snoc cpas cpa

let ae_cipher = AES.iv_cipher * MAC.tag
let ae_as_mac (c:ae_cipher) = MAC.Entry (fst c) (snd c)

/// A lemma that shows that if a cipher is MAC'd
/// then a corresponding entry must exists in the CPA log
let rec mac_only_cpa_ciphers_mem (macs:Seq.seq MAC.log_entry) 
                                 (cpas:Seq.seq CPA.log_entry)
                                 (c:ae_cipher)
    : Lemma (requires (mac_only_cpa_ciphers macs cpas /\
                       Seq.mem (ae_as_mac c) macs))
            (ensures (exists p. Seq.mem (CPA.Entry p (fst c)) cpas))
            (decreases (Seq.length macs))
    = if Seq.length macs = 0 then
         ()
      else let macs, mac = un_snoc macs in
           let cpas, cpa = un_snoc cpas in
           Seq.lemma_mem_snoc macs mac;
           Seq.lemma_mem_snoc cpas cpa;
           if mac = ae_as_mac c then ()
           else mac_only_cpa_ciphers_mem macs cpas c

let ae = Ideal.uf_cma

/// The main invariant:
///     -- A conjunction of the 3 components already mentioned
///      + some technical invariants about logs being allocated
let invariant k h =
  CPA.invariant k.enc h /\
  MAC.invariant k.mac h /\
  (ae ==> mac_only_cpa_ciphers (mac_log h k) (cpa_log h k))

let log_entry = Plain.plain & ae_cipher

let composite_log_entry (mac:MAC.log_entry) (cpa:CPA.log_entry) : log_entry =
  (cpa.CPA.plain, (cpa.CPA.c, mac.MAC.tag))  
  
let rec composite_log (macs:Seq.seq MAC.log_entry) 
                      (cpas:Seq.seq CPA.log_entry{mac_only_cpa_ciphers macs cpas})
  : Tot (aes:Seq.seq log_entry{Seq.length aes = Seq.length macs}) (decreases (Seq.length macs))
  = if Seq.length macs = 0 then Seq.empty
    else let macs, mac = un_snoc macs in
         let cpas, cpa = un_snoc cpas in
         Seq.snoc (composite_log macs cpas) (composite_log_entry mac cpa)

let composite_log_snoc
       (macs:Seq.seq MAC.log_entry) 
       (mac:MAC.log_entry)
       (cpas:Seq.seq CPA.log_entry)
       (cpa:CPA.log_entry{
         mac_only_cpa_ciphers macs cpas /\
         mac_only_cpa_ciphers (snoc macs mac) (snoc cpas cpa)})
  : Lemma (composite_log (snoc macs mac) (snoc cpas cpa) ==
           snoc (composite_log macs cpas) (composite_log_entry mac cpa))
  = un_snoc_snoc macs mac;
    un_snoc_snoc cpas cpa

let ae_log (k:key) (h:mem{invariant k h /\ ae}) =
  composite_log (MAC.log k.mac h) (CPA.log k.enc h)

(*** The main AE lemma relying on the invariant  ***)

(** For logs that respect the main invariant:
//        if  (c, t) is a valid MAC
//        and (p, c) is a valid CPA
//        then (p, (c, t)) must be a in the AE log

//     The pairwise distinctness of ciphers in the CPA log
//     plays a crucial role.

//     For instance, using it, and knowing that (c, t) is a valid MAC, 
//     we can conclude that their must be exactly one entry 
//     in the CPA table containing c. **)
let rec invert_invariant_aux (macs:Seq.seq MAC.log_entry)
                             (cpas:Seq.seq CPA.log_entry)
                             (c:ae_cipher) (p:Plain.plain)
   : Lemma 
     (requires 
       mac_only_cpa_ciphers macs cpas /\
       CPA.pairwise_distinct_ivs cpas /\
       Seq.mem (ae_as_mac c) macs /\
       Seq.mem (CPA.Entry p (fst c)) cpas)
     (ensures
       Seq.mem (p, c) (composite_log macs cpas))
     (decreases (Seq.length macs))
   = let aes = composite_log macs cpas in
     assert (Seq.length macs == Seq.length aes);
     if Seq.length macs = 0 then ()
     else let macs, mac = un_snoc macs in
          let cpas, cpa = un_snoc cpas in
          assert (CPA.pairwise_distinct_ivs (snoc cpas cpa));          
          let aes,   ae = un_snoc aes  in
          Seq.lemma_mem_snoc aes ae;
          Seq.lemma_mem_snoc macs mac;
          Seq.lemma_mem_snoc cpas cpa;
           if mac = ae_as_mac c then begin
             assert (cpa.CPA.c == fst c);
             CPA.invert_pairwise cpas cpa (fst c);
             assert (not (Seq.mem (CPA.Entry p (fst c)) cpas));
             assert (CPA.Entry?.plain cpa == p);
             assert (ae = (p, c))
           end
           else if mac.MAC.msg = fst c then begin
             assert (CPA.Entry?.c cpa == fst c);
             mac_only_cpa_ciphers_mem macs cpas c;
             assert (exists q1. Seq.mem (CPA.Entry q1 (fst c)) cpas);
             CPA.invert_pairwise cpas cpa (fst c)
           end
           else begin
             mac_only_cpa_ciphers_snoc macs mac cpas cpa;
             CPA.pairwise_snoc cpas cpa;
             invert_invariant_aux macs cpas c p;
             assert (Seq.mem (p, c) (composite_log macs cpas));
             composite_log_snoc macs mac cpas cpa;
             Seq.lemma_mem_snoc (composite_log macs cpas) (composite_log_entry mac cpa)
           end

/// Lifting the lemma above to work on the current state, h
let invert_invariant (h:mem) (k:key) (c:ae_cipher) (p:Plain.plain)
  : Lemma 
    (requires 
      ae /\
      invariant k h /\
      Seq.mem (ae_as_mac c) (mac_log h k) /\
      Seq.mem (CPA.Entry p (fst c)) (cpa_log h k))
    (ensures 
      Seq.mem (p, c) (ae_log k h))
    = let macs = mac_log h k in
      let cpas = cpa_log h k in
      let aes  = ae_log k h in
      invert_invariant_aux macs cpas c p

(*** Main interface of AE
     keygen, encrypt, decrypt ***)

/// keygen: create a fresh key in the caller's region
///         its ae log is initially empty
let keygen ()
  : ST key
  (requires fun _ -> True)
  (ensures  fun h0 k h1 ->
    B.modifies B.loc_none h0 h1 /\
    invariant k h1) =
  let ke = CPA.keygen () in
  let ka = MAC.keygen () in
  Key ka ke


/// encrypt:
///       We return a cipher, preserve the invariant,
///       and extend the log by exactly one entry
let encrypt (k:key) (plain:Plain.plain)
  : ST ae_cipher
  (requires 
    invariant k)
  (ensures  fun h0 c h1 ->
    invariant k h1 /\
    B.modifies (B.loc_union (B.loc_mreference k.mac.MAC.log)
                            (B.loc_mreference k.enc.CPA.log)) h0 h1 /\
    (ae ==> ae_log k h1 == Seq.snoc (ae_log k h0) (plain, c))) =
  let h0 = FStar.HyperStack.ST.get () in
  let c = CPA.encrypt k.enc plain in
  let h1 = FStar.HyperStack.ST.get () in
  let t = MAC.mac k.mac c in
  let h2 = get () in
  assert (cpa_log h2 k == cpa_log h1 k);
  assert (CPA.invariant k.enc h2); 
  assert (MAC.invariant k.mac h2); 
  mac_only_cpa_ciphers_snoc (mac_log h0 k) (MAC.Entry c t)
                            (cpa_log h0 k) (CPA.Entry plain c);
  if ae then 
    composite_log_snoc (mac_log h0 k)  (MAC.Entry c t)
                       (cpa_log h0 k) (CPA.Entry plain c);
  (c, t)

/// decrypt:
///     In the ideal case, we prove it functionally correct and secure
///     meaning that we the plain text returned is exactly the one in in AE log
let decrypt (k:key) (c:ae_cipher)
  : ST (option Plain.plain)
  (requires 
    invariant k)
  (ensures fun h0 res h1 ->
    invariant k h1 /\
    h0 == h1 /\
    (ae ==>
     (match res with
      | Some plain -> ae_log k h1 `Log.has` (plain, c)
      | None -> True))) = //forall plain. ~ (ae_log k h1 `Log.has` (plain, c))))) =
  let h = get() in
  let c, tag = c in
  if MAC.verify k.mac c tag
  then begin
       if ae then mac_only_cpa_ciphers_mem (mac_log h k) (cpa_log h k) (c, tag);
       let p = CPA.decrypt k.enc c in
       if ae then invert_invariant h k (c,tag) p;
       Some p
  end
  else None

