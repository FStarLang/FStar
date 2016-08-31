module EtM.MAC

open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.Monotonic.RRef




open Platform.Bytes
open CoreCrypto

type text = EtM.CPA.cipher 

let keysize   = 1
let blocksize = keysize
let macsize   = hashSize SHA1

type sha1_key = lbytes keysize
type tag = lbytes macsize




val sha1: bytes -> Tot (h:bytes{length h = 20})
let sha1 b = hash SHA1 b

val hmac_sha1: sha1_key -> text -> Tot tag
let hmac_sha1 k t =
  let x5c = byte_of_int 92 in
  let x36 = byte_of_int 54 in
  let opad = createBytes blocksize x5c in
  let ipad = createBytes blocksize x36 in
  let xor_key_opad = xor keysize k opad in
  let xor_key_ipad = xor keysize k ipad in
  sha1 (xor_key_opad @| (sha1 (xor_key_ipad @| t)))

(* ------------------------------------------------------------------------ *)
type property = text -> Type0

type msg = text

type log_t (r:rid) = Monotonic.Seq.log_t r (msg * tag)

noeq type key =
  | Key: #region:rid -> raw:sha1_key -> log:log_t region -> key


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

val mac: k:key -> m:msg -> ST tag
  (requires (fun m0 -> True))
  (ensures  (fun m0 t m1 ->
    (let log0 = m_sel m0 k.log in
     let log1 = m_sel m1 k.log in
     let n = Seq.length log0 in
       modifies_one k.region m0 m1
     /\ m_contains k.log m1
     /\ log1 == snoc log0 (m, t)
     /\ witnessed (at_least n (m, t) k.log)
     /\ Seq.length log1 == Seq.length log0 + 1
     )))

let mac k m =
  let ilog = m_read k.log in
  let t = hmac_sha1 k.raw m in
  write_at_end k.log (m,t);
  t


val verify: k:key -> m:msg -> t:tag -> ST bool
  (requires (fun h ->  Map.contains h k.region ))
  (ensures  (fun m0 b m1 ->
     modifies_none m0 m1 /\
     (let log = m_sel m0 k.log in
      ( (b2t Ideal.uf_cma) /\ b) ==> is_Some (seq_find (fun mt -> mt = (m,t)) log))))

let verify k m t =
  let t' = hmac_sha1 k.raw m in
  let verified = (t = t') in
  let log = m_read k.log in
  let found = is_Some (seq_find (fun mt -> mt = (m,t)) log) in
  if Ideal.uf_cma then
    verified && found
  else
    verified

