module EtM.CPA

open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.Monotonic.RRef
open EtM.Ideal


open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes

open EtM.Plain

type ivsize = blockSize AES_128_CBC
type keysize = 16
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
type msg = plain
type cipher = b:bytes{B.length b >= ivsize}
(* MK: minimal cipher length twice blocksize? *)

type log_t (r:rid) = Monotonic.Seq.log_t r (msg * cipher)

noeq type key =
  | Key: #region:rid -> raw:aes_key -> log:log_t region -> key

let genPost parent m0 (k:key) m1 =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ fresh_region k.region m0 m1
  /\ m_contains k.log m1
  /\ m_sel m1 k.log == createEmpty

val keygen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))

let keygen parent =
  let raw = random keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #region raw log

val encrypt: k:key -> m:msg -> ST cipher
  (requires (fun h0 -> True (* If we wanted to avoid recall:
                               m_contains k.log h0 *)))
  (ensures  (fun h0 c h1 ->
    (let log0 = m_sel h0 k.log in
     let log1 = m_sel h1 k.log in
      modifies_one k.region h0 h1 /\
      m_contains k.log h1
     /\ log1 == snoc log0 (m, c)
     /\ witnessed (at_least (Seq.length log0) (m, c) k.log))))


let encrypt k m : cipher =
  m_recall k.log;
  let iv = random ivsize in
  let text = if ind_cpa then createBytes (length m) 0z else repr m in
  let c = CoreCrypto.block_encrypt AES_128_CBC k.raw iv text in
  let c = iv@|c in
  write_at_end k.log (m,c);
  c


val decrypt: k:key -> c:cipher -> ST msg
  (requires (fun h0 ->
    Map.contains h0 k.region /\
    (let log0 = m_sel h0 k.log in
      (b2t ind_cpa_rest_adv) ==> is_Some (seq_find (fun mc -> snd mc = c) log0))))
  (ensures  (fun h0 res h1 ->
    modifies_none h0 h1 /\
    ( (b2t ind_cpa_rest_adv) ==> SeqProperties.mem (res,c) (m_sel h0 k.log)
     (* (let log0 = m_sel h0 k.log in *)
     (*  let found = seq_find (fun mc -> snd mc = c) log0 in *)
     (*  is_Some found /\ fst (Some.v found) = res) *)
    )
  )
  )

let decrypt k c =
  if ind_cpa_rest_adv then
    let log = m_read k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> fst mc
  else
    let iv,c' = split c ivsize in
    coerce (CoreCrypto.block_decrypt AES_128_CBC k.raw iv c')
