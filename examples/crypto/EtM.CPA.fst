module EtM.CPA
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open EtM.Ideal

open Platform.Bytes
module CC = EtM.CoreCrypto
module B = Platform.Bytes

open EtM.Plain

let ivsize = CC.blockSize CC.AES_128_CBC
let iv = lbytes ivsize
let keysize = 16
let aes_key = lbytes keysize
let msg = plain
let cipher = (b:bytes{B.length b >= ivsize})
  (* MK: minimal cipher length twice blocksize? *)

type log_entry =
  | Entry: plain:msg
         -> c:cipher
         -> log_entry

let iv_of_entry (Entry _ c) : iv = fst (B.split c ivsize)
let raw_cipher (Entry _ c) : bytes = snd (B.split c ivsize)
let split_entry (p:plain) (c:cipher) (iv:iv) (r:bytes)
   : Lemma  (iv_of_entry (Entry p (iv@|r)) == iv /\
             raw_cipher  (Entry p (iv@|r)) == r)
   = admit()

let log_t (r:rid) =
    Monotonic.Seq.log_t r log_entry

noeq 
type key =
  | Key: #region:rid -> raw:aes_key -> log:log_t region -> key

let log (k:key) (h:mem) 
  : GTot (seq log_entry) =
    m_sel h (Key?.log k)

let pairwise_distinct_ivs (log:seq log_entry) =
    forall (e1:log_entry{Seq.mem e1 log}) 
      (e2:log_entry{Seq.mem e2 log}). {:pattern Seq.mem e1 log; Seq.mem e2 log}
        e1 <> e2 ==> iv_of_entry e1 <> iv_of_entry e2

let entry_functional_correctness (raw_key:bytes) (e:log_entry) : Type0 =
    let iv = iv_of_entry e in
    let c = raw_cipher e in
    let plain = Entry?.plain e in
    //cipher text is an encryption of plain and iv
    let p = if ind_cpa then createBytes (length plain) 0z else repr plain in
     c == CC.block_encrypt_spec CC.AES_128_CBC raw_key iv p

let cipher_functional_correctness (raw_key:bytes) (log:seq log_entry) =
    forall (e:log_entry{Seq.mem e log}). {:pattern (Seq.mem e log)}
      entry_functional_correctness raw_key e

let invariant (k:key) (h:mem) =
    let Key raw_key lg = k in
    let log = log k h in
    m_contains lg h /\
    pairwise_distinct_ivs log /\
    cipher_functional_correctness raw_key log

let ivs (k:key) 
  : ST (Set.set iv)
       (fun h -> True)
       (fun h0 ivs h1 -> h0 == h1 /\
                      (forall i. indexable (log k h1) i ==> 
                            iv_of_entry (Seq.index (log k h1) i) `Set.mem` ivs))
  = admit()

let genPost parent (m0:mem) (k:key) (m1:mem) =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ stronger_fresh_region k.region m0 m1
  /\ log k m1 == createEmpty
  /\ invariant k m1
  
val keygen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))
let keygen parent =
  let raw = CC.rand keysize FStar.Set.empty in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #region raw log

val encrypt: k:key -> m:msg -> ST cipher
  (requires (invariant k))
  (ensures  (fun h0 c h1 ->
    (let log0 = log k h0 in
     let log1 = log k h1 in
     invariant k h1 /\
     modifies_one k.region h0 h1 /\
     m_contains k.log h1 /\
     log1 == snoc log0 (Entry m c))))
let encrypt k m =
  let ivs = ivs k in
  let iv = CC.rand ivsize ivs in
  let text = if ind_cpa // && ind_cpa_rest_adv
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
  assume (pairwise_distinct_ivs (log k h1));
  c

val decrypt: k:key -> c:cipher -> ST msg
  (requires (fun h0 ->
    let log = log k h0 in
    invariant k h0 /\
    (b2t ind_cpa_rest_adv ==> (exists p. Seq.mem (Entry p c) log))))
  (ensures  (fun h0 res h1 ->
    let log = log k h1 in
    modifies_none h0 h1 /\
    invariant k h1 /\
    (b2t ind_cpa_rest_adv ==> Seq.mem (Entry res c) log)))

let entry_has_cipher (c:cipher) (e:log_entry) = Entry?.c e = c

let find_entry (log:seq log_entry) (c:cipher) : Pure log_entry
    (requires (exists p. Seq.mem (Entry p c) log))
    (ensures (fun e -> Seq.mem e log /\ entry_has_cipher c e))
  = let eopt = Seq.seq_find (entry_has_cipher c) log in
    FStar.Classical.exists_elim
             (Some? eopt /\ Seq.mem (Some?.v eopt) log /\ entry_has_cipher c (Some?.v eopt))
             ()
             (fun (p:plain{Seq.mem (Entry p c) log}) -> 
                Seq.find_mem log (entry_has_cipher c) (Entry p c));
    Some?.v eopt                
  
let decrypt k c =
  let Key raw_key log = k in
  let iv,c' = split c ivsize in
  let raw_plain = CC.block_dec CC.AES_128_CBC raw_key iv c' in
  if ind_cpa_rest_adv then
    let log = m_read log in
    let eopt = seq_find (entry_has_cipher c) log in
    let Entry plain _ = find_entry log c in
    split_entry plain c iv c';
    if not ind_cpa then begin
       //no correction necessary
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
