module EtM.CPA

open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.Monotonic.RRef


open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes

open EtM.Plain

type ivsize = blockSize AES_128_CBC
type keysize = 16
type aes_key = lbytes keysize
type msg = plain
type cipher = l:bytes{B.length l >= ivsize}

type log_t (r:rid) = Monotonic.Seq.log_t r (msg * cipher)

noeq type key =
  | Key: #region:rid -> raw:aes_key -> log:log_t region -> key

let genPost parent m0 (k:key) m1 =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ fresh_region k.region m0 m1
  /\ m_contains k.log m1
  /\ m_sel m1 k.log == createEmpty

val gen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))

let gen parent =
  let raw = random keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #region raw log

val encrypt: k:key -> m:msg -> ST cipher
  (requires (fun _ -> True))
  (ensures  (fun m0 c m1 ->
    (let ilog = m_sel m0 k.log in
     let n = Seq.length ilog in
       modifies_one k.region m0 m1
     /\ m_contains k.log m1
     /\ m_sel m1 k.log == snoc ilog (m, c)
     /\ witnessed (at_least n (m, c) k.log))))


let encrypt k m =
  m_recall k.log;
  let iv = random ivsize in
  let ilog = m_read k.log in
  let text = if ind_cpa then createBytes (length m) 0z else repr m in
  let c = CoreCrypto.block_encrypt AES_128_CBC k.raw iv text in
  let c = iv@|c in
  assert(B.length c >= ivsize);
  write_at_end k.log (m,c);
  c
  

val decrypt: k:key -> c:cipher -> ST msg
  (requires (fun h0 ->
    (let log = m_sel h0 k.log in
     is_Some (seq_find (fun mc -> snd mc = c) log))))
  (ensures  (fun m0 res m1 ->
    ind_cpa ==>
     (let log = m_sel m0 k.log in
      let found = seq_find (fun mc -> snd mc = c) log in
      is_Some found ==> (let Some mc = found in res = fst mc))))

let decrypt k c =
  if ind_cpa then
    let log = m_read k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> fst mc
  else
    let iv,c' = split c ivsize in
    coerce (CoreCrypto.block_decrypt AES_128_CBC k.raw iv c')
