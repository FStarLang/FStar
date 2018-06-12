module EtM.AE
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

module MAC = EtM.MAC

open Platform.Bytes
open CoreCrypto
module CPA = EtM.CPA
module MAC = EtM.MAC
module Ideal = EtM.Ideal
module Plain = EtM.Plain

(*** Basic types ***)

type rid = erid

/// An AE cipher includes a mac tag
type cipher = (CPA.cipher * MAC.tag)

/// An AE log pairs plain texts with MAC'd ciphers
let log_entry = Plain.plain * cipher
type log_t (r:rid) = m_rref r (seq log_entry) grows

/// An AE key pairs an encryption key, ke, with a MAC'ing key, km,
/// with an invariant ensuring that their memory footprints of their
/// ideal state are disjoint.
/// 
/// Aside from this, we have an AE log, which is a view of the two
/// other logs.
noeq type key =
  | Key: #region:rid
       -> ke:CPA.key { extends (CPA.Key?.region ke) region  }
       -> km:MAC.key { extends (MAC.Key?.region km) region /\
                      disjoint( CPA.Key?.region ke) (MAC.Key?.region km) } 
       -> log:log_t region
       -> key

(** Accessors for the three logs **)
/// ae log
let get_log (h:mem) (k:key) =
  sel h k.log

/// mac log
let get_mac_log (h:mem) (k:key) =
  sel h (MAC.Key?.log k.km)

/// cpa log
let get_cpa_log (h:mem) (k:key) =
  sel h (CPA.Key?.log k.ke)

(*** Main invariant on the ideal state ***)
(** There are three components to this invariant

    1. The CPA invariant (pairwise distinctness of IVs, notably)

    2. mac_only_cpa_ciphers: 
       
       The MAC log and CPA logs are related, in that the MAC log only
       contains entries for valid ciphers recorded the CPA log

    3. mac_and_cpa_refine_ae: 

       The AE log is a combined view of the MAC and CPA logs Each of
       its entries corresponds is combination of a single entry in the
       MAC log and another in the CPA log 
**)

let mac_cpa_related (mac:EtM.MAC.log_entry) (cpa:EtM.CPA.log_entry) =
  CPA.Entry?.c cpa == fst mac

/// See the comment above, for part 2 of the invariant
///   -- As in EtM.CPA, we state the invariant recursively
///      matching entries up pointwise
let rec mac_only_cpa_ciphers (macs:Seq.seq EtM.MAC.log_entry) 
                             (cpas:Seq.seq EtM.CPA.log_entry)
      : Tot Type0 (decreases (Seq.length macs)) =
   Seq.length macs == Seq.length cpas /\
   (if Seq.length macs > 0 then
     let macs, mac = Seq.un_snoc macs in
     let cpas, cpa = Seq.un_snoc cpas in
     mac_cpa_related mac cpa /\
     mac_only_cpa_ciphers macs cpas
    else True)

/// A lemma to intro/elim the recursive predicate above
let mac_only_cpa_ciphers_snoc (macs:Seq.seq EtM.MAC.log_entry) (mac:EtM.MAC.log_entry)
                                     (cpas:Seq.seq EtM.CPA.log_entry) (cpa:EtM.CPA.log_entry)
  : Lemma (mac_only_cpa_ciphers (snoc macs mac) (snoc cpas cpa) <==>
          (mac_only_cpa_ciphers macs cpas /\ mac_cpa_related mac cpa))
  = un_snoc_snoc macs mac;
    un_snoc_snoc cpas cpa

/// A lemma that shows that if an cipher is MAC'd
/// then a corresponding entry must exists in the CPA log
let rec mac_only_cpa_ciphers_mem (macs:Seq.seq EtM.MAC.log_entry) 
                                 (cpas:Seq.seq EtM.CPA.log_entry)
                                 (c:cipher)
    : Lemma (requires (mac_only_cpa_ciphers macs cpas /\
                       Seq.mem c macs))
            (ensures (exists p. Seq.mem (CPA.Entry p (fst c)) cpas))
            (decreases (Seq.length macs))
    = if Seq.length macs = 0 then
         ()
      else let macs, mac = un_snoc macs in
           let cpas, cpa = un_snoc cpas in
           Seq.lemma_mem_snoc macs mac;
           Seq.lemma_mem_snoc cpas cpa;
           if mac = c then ()
           else mac_only_cpa_ciphers_mem macs cpas c

/// See part 3 of the invariant:
///     -- An AE entry is related to a MAC and CPA entry
///        if its plain text + cipher appears in the CPA entry
///        and its cipher+tag appear in the MAC table
let mac_and_cpa_refine_ae_entry (ae:log_entry)
                                (mac:EtM.MAC.log_entry)
                                (cpa:EtM.CPA.log_entry) =
    let p, c = ae in
    mac == c /\
    CPA.Entry p (fst c) == cpa

/// See part 3 of the invariant:
///     -- A pointwise lifting the relation between the entries in the three logs
let rec mac_and_cpa_refine_ae (ae_entries:Seq.seq log_entry) 
                              (mac_entries:Seq.seq EtM.MAC.log_entry)
                              (cpa_entries:Seq.seq EtM.CPA.log_entry)
        : Tot Type0 (decreases (Seq.length ae_entries)) =
  Seq.length ae_entries == Seq.length mac_entries /\
  Seq.length mac_entries == Seq.length cpa_entries /\
  (if Seq.length ae_entries <> 0
   then let ae_prefix, ae_last = Seq.un_snoc ae_entries in
        let mac_prefix, mac_last = Seq.un_snoc mac_entries in
        let cpa_prefix, cpa_last = Seq.un_snoc cpa_entries in
        mac_and_cpa_refine_ae_entry ae_last mac_last cpa_last /\
        mac_and_cpa_refine_ae ae_prefix mac_prefix cpa_prefix
   else True)

/// A lemma to intro/elim the recursive predicate above
let mac_and_cpa_refine_ae_snoc (ae_entries:Seq.seq log_entry) 
                               (mac_entries:Seq.seq EtM.MAC.log_entry)
                               (cpa_entries:Seq.seq EtM.CPA.log_entry)
                               (ae:log_entry)
                               (mac:EtM.MAC.log_entry)
                               (cpa:EtM.CPA.log_entry)
    : Lemma (mac_and_cpa_refine_ae (snoc ae_entries ae)
                                   (snoc mac_entries mac)
                                   (snoc cpa_entries cpa) <==>
            (mac_and_cpa_refine_ae ae_entries mac_entries cpa_entries /\
             mac_and_cpa_refine_ae_entry ae mac cpa))
    = Seq.un_snoc_snoc ae_entries ae;
      Seq.un_snoc_snoc mac_entries mac;
      Seq.un_snoc_snoc cpa_entries cpa

/// The main invariant:
///     -- A conjunction of the 3 components already mentioned
///      + some technical invariants about logs being allocated
let invariant (h:mem) (k:key) =
  let log = get_log h k in
  let mac_log = get_mac_log h k in
  let cpa_log = get_cpa_log h k in
  Map.contains (get_hmap h) k.region /\
  Map.contains (get_hmap h) (MAC.Key?.region k.km) /\
  Map.contains (get_hmap h) (CPA.Key?.region k.ke) /\
  EtM.CPA.invariant (Key?.ke k) h /\
  mac_only_cpa_ciphers (get_mac_log h k) (get_cpa_log h k) /\
  mac_and_cpa_refine_ae (get_log h k) (get_mac_log h k) (get_cpa_log h k)

(*** The main AE lemma relying on the invariant  ***)

(** For logs that respect the main invariant:
       if  (c, t) is a valid MAC
       and (p, c) is a valid CPA
       then (p, (c, t)) must be a in the AE log

    The pairwise distinctness of ciphers in the CPA log
    plays a crucial role.

    For instance, using it, and knowing that (c, t) is a valid MAC, 
    we can conclude that their must be exactly one entry 
    in the CPA table containing c. **)
let rec invert_invariant_aux (c:cipher) (p:Plain.plain)
                             (macs:Seq.seq MAC.log_entry)
                             (cpas:Seq.seq CPA.log_entry)
                             (aes :Seq.seq log_entry)
    : Lemma (requires (mac_only_cpa_ciphers macs cpas /\
                       mac_and_cpa_refine_ae aes macs cpas /\
                       CPA.pairwise_distinct_ivs cpas /\
                       Seq.mem c macs /\
                       Seq.mem (CPA.Entry p (fst c)) cpas))
            (ensures (Seq.mem (p, c) aes))
            (decreases (Seq.length macs))
    = assert (Seq.length macs == Seq.length aes);
      if Seq.length macs = 0 then ()
      else let macs, mac = un_snoc macs in
           let cpas, cpa = un_snoc cpas in
           let aes,   ae = un_snoc aes  in
           Seq.lemma_mem_snoc aes ae;
           Seq.lemma_mem_snoc macs mac;
           Seq.lemma_mem_snoc cpas cpa;
           if mac = c then begin
             assert (CPA.Entry?.c cpa == fst c);
             CPA.invert_pairwise cpas cpa (fst c);
             assert (not (Seq.mem (CPA.Entry p (fst c)) cpas));
             assert (CPA.Entry?.plain cpa == p);
             assert (ae = (p, c))
           end
           else if fst mac = fst c then begin
             assert (CPA.Entry?.c cpa == fst c);
             mac_only_cpa_ciphers_mem macs cpas c;
             assert (exists q1. Seq.mem (CPA.Entry q1 (fst c)) cpas);
             CPA.invert_pairwise cpas cpa (fst c)
           end
           else begin
             assert (mac_and_cpa_refine_ae aes macs cpas);
             mac_only_cpa_ciphers_snoc macs mac cpas cpa;
             CPA.pairwise_snoc cpas cpa;
             invert_invariant_aux c p macs cpas aes
           end

/// Lifting the lemma above to work on the current state, h
let invert_invariant (h:mem) (k:key) (c:cipher) (p:Plain.plain)
    : Lemma (requires (invariant h k /\
                       Seq.mem c (get_mac_log h k) /\
                       Seq.mem (CPA.Entry p (fst c)) (get_cpa_log h k)))
            (ensures (Seq.mem (p, c) (get_log h k)))
    = let macs = get_mac_log h k in
      let cpas = get_cpa_log h k in
      let aes  = get_log h k in
      invert_invariant_aux c p macs cpas aes

(*** Main interface of AE
       keygen, encrypt, decrypt ***)

/// keygen: create a fresh key in the caller's region
///         its ae log is initially empty
let keygen (parent:rid)
  : ST key
  (requires (fun _ -> HyperStack.ST.witnessed (region_contains_pred parent)))
  (ensures  (fun h0 k h1 ->
    modifies Set.empty h0 h1    /\
    extends k.region parent     /\
    fresh_region k.region h0 h1 /\
    Map.contains (get_hmap h1) k.region /\
    contains h1 k.log /\
    sel h1 k.log == createEmpty /\
    invariant h1 k)) =
  let region = new_region parent in
  let ke = CPA.keygen region in
  let ka = MAC.keygen region in
  let log = alloc_mref_seq region createEmpty in
  Key #region ke ka log

/// encrypt:
///       We return a cipher, preserve the invariant,
///       and extend the log by exactly one entry
#set-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1 --z3rlimit 30"
let encrypt (k:key) (plain:Plain.plain)
  : ST cipher
  (requires (fun h0 -> invariant h0 k))
  (ensures  (fun h0 c h1 ->
    (let log0 = get_log h0 k in
     let log1 = get_log h1 k in
     modifies_transitively (Set.singleton k.region)  h0 h1
     /\ invariant h1 k
     /\ log1 == snoc log0 (plain, c)))) =
  let h0 = FStar.HyperStack.ST.get () in
  let c = CPA.encrypt k.ke plain in
  let t = MAC.mac k.km c in
  write_at_end k.log (plain, (c, t));
  let h1 = FStar.HyperStack.ST.get () in
  assert (sel h1 k.log == snoc (sel h0 k.log) (plain, (c, t)));
  assert (EtM.CPA.invariant (Key?.ke k) h1);
  mac_and_cpa_refine_ae_snoc (get_log h0 k) (get_mac_log h0 k) (get_cpa_log h0 k)
                             (plain, (c,t)) (c,t) (CPA.Entry plain c);
  mac_only_cpa_ciphers_snoc (get_mac_log h0 k) (c,t)
                            (get_cpa_log h0 k) (CPA.Entry plain c);
  (c, t)

/// decrypt:
///     In the ideal case, we prove it functionally correct and secure
///     meaning that we the plain text returned is exactly the one in in AE log
let decrypt (k:key) (c:cipher)
  : ST (option Plain.plain)
  (requires (fun h0 -> invariant h0 k))
  (ensures (fun h0 res h1 ->
    modifies_none h0 h1 /\
    invariant h1 k /\
    (b2t Ideal.uf_cma /\ Some? res ==>
     Seq.mem (Some?.v res, c) (get_log h0 k)))) =
  let c, tag = c in
  let h0 = FStar.HyperStack.ST.get () in
  if MAC.verify k.km c tag
  then begin
       if Ideal.uf_cma then mac_only_cpa_ciphers_mem (get_mac_log h0 k) (get_cpa_log h0 k) (c, tag);
       let p = CPA.decrypt k.ke c in
       if Ideal.uf_cma then 
         (let h = FStar.HyperStack.ST.get() in
          invert_invariant h k (c,tag) p);
       Some p
  end
  else None
