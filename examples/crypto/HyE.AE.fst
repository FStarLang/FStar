module HyE.AE

open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open HyE.Flags
open HyE.Indexing

open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes

// Import HyE.PlainAE later, so we have that Plain.t is actually of type bytes.
open HyE.PlainAE

let ivsize = aeadRealIVSize AES_128_GCM
type keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
type msg = protected_ae_plain
type cipher = b:bytes{B.length b >= ivsize}
(* MK: minimal cipher length twice blocksize? *)

type log_t (r:rid) = m_rref r (seq (msg * cipher)) grows

noeq abstract type key =
  | Key: #i:id -> #region:rid -> raw:aes_key -> log:log_t region -> honest:bool-> key

val getIndex: k:key -> Tot id
let getIndex k =
  k.i

let safe_key_gen parent m0 (k:key) m1 =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ fresh_region k.region m0.h m1.h
  /\ m_contains k.log m1

(**
   This function generates a key in a fresh region of memory below the parent region.
   The postcondition ensures that the log is empty after creation.
*)
val keygen: i:id -> parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 -> 
    safe_key_gen parent h0 k h1
    /\ m_sel h1 k.log == createEmpty
    ))

let keygen i parent =
  let raw = random keysize in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #i #region raw log true

(**
   The leak function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
val leak: k:key{not (honest k.i)} -> Tot aes_key 
let leak k =
  k.raw

(**
   The coerce function transforms a raw aes_key into an abstract key. The function is stateful,
   as we need to allocate space in memory for the key. The refinement type on the key makes sure that
   abstract keys created this way can not be honest.
*)
val coerce_key: i:id{not (honest i) } -> parent:rid -> aes_key -> ST key
  (requires (fun _ -> True))
  (ensures  (safe_key_gen parent))
let coerce_key i parent raw = 
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #i #region raw log false

type safe_log_append k fst h0 snd h1 =
    modifies_one k.region h0 h1 
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == snoc (m_sel h0 k.log) (fst, snd)
    /\ witnessed (at_least (Seq.length (m_sel h0 k.log)) (fst, snd) k.log)

// Should the precondition not be guaranteed by the key type? Same thing in decrypt.
val encrypt: k:key -> m:msg -> ST cipher
  (requires (fun h0 -> 
    getIndex k = PlainAE.getIndex m(*m_contains k.log h0*)))
  (ensures  (safe_log_append k m))

(* There is currently no check for int-ctxt*)
let encrypt k m : cipher =
  m_recall k.log;
  let iv = random ivsize in
  let text = if (ae_ind_cca && honest k.i) then createBytes (length m) 0z else (repr m) in
  let c = CoreCrypto.aead_encrypt AES_128_GCM k.raw iv empty_bytes text in
  let c = iv@|c in
  write_at_end k.log (m,c);
  c


val decrypt: k:key -> c:cipher -> ST (option msg)
  (requires (fun h -> True (* Could require Map.contains h0 k.region *)))
  (ensures  (fun h0 res h1 -> //True))
    modifies_none h0 h1
    /\ ( (b2t ae_int_ctxt /\ honest k.i /\ Some? res) ==> SeqProperties.mem (Some?.v res,c) (m_sel h0 k.log) )
    ))
let decrypt k c =
  if ae_int_ctxt && honest k.i then
    let log = m_read k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> Some (fst mc)
    | None -> None
  else
    let iv,c' = split c ivsize in
    assume( B.length c' >= aeadTagSize AES_128_GCM);
    let poption = (CoreCrypto.aead_decrypt AES_128_GCM k.raw iv empty_bytes c') in
    if Some? poption then
      Some (PlainAE.coerce #k.i (Some?.v poption))
    else
      None
