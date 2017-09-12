module HyE.AE
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open HyE.Ideal

open Platform.Bytes
open CoreCrypto
module CC = CoreCrypto
module B = Platform.Bytes

open HyE.Plain
module Plain = HyE.Plain

let ivsize = aeadRealIVSize AES_128_GCM
let keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
type msg = Plain.t
type cipher = b:bytes{B.length b >= ivsize}
(* MK: minimal cipher length twice blocksize? *)

type log_t (r:rid) = m_rref r (seq (msg * cipher)) grows

noeq abstract type key =
  | Key: #region:rid -> raw:aes_key -> log:log_t region -> key


let genPost parent m0 (k:key) m1 =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ fresh_region k.region m0.h m1.h
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

val leak: k:key{not conf} -> Tot aes_key 
let leak k =
  k.raw

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

let encrypt k m =
  m_recall k.log;
  let iv = random ivsize in
  let text = if ind_cca && int_ctxt then createBytes (length m) 0z else repr m in
  let c = CC.aead_encrypt AES_128_GCM k.raw iv empty_bytes text in
  let c = iv@|c in
  write_at_end k.log (m,c);
  c


(* this doesn't really belong here *)
val mem : #a:eqtype -> x:a -> xs:Seq.seq a -> Tot bool
let mem (#a:eqtype) x xs = Some? (Seq.seq_find (fun y -> y = x) xs)

val decrypt: k:key -> c:cipher -> ST (option msg)
  (requires (fun h0 -> True (* Could require Map.contains h0 k.region *)
    ))
  (ensures  (fun h0 res h1 ->
    modifies_none h0 h1 /\
    ( (b2t int_ctxt /\ Some? res) ==> mem (Some?.v res,c) (m_sel h0 k.log)
    )
  )
  )


let decrypt k c =
  if int_ctxt then
    let log = m_read k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> Some (fst mc)
    | None -> None
  else
    let iv,c' = split c ivsize in
    assume( B.length c' >= aeadTagSize AES_128_GCM);
    let poption = (CC.aead_decrypt AES_128_GCM k.raw iv empty_bytes c') in
    if Some? poption then
      Some (coerce (Some?.v poption))
    else
      None
