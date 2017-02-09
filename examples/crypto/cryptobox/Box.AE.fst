module Box.AE

open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperStack
open FStar.HyperHeap
open FStar.Monotonic.RRef

open Box.Flags
open Box.Indexing

open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
open Box.PlainAE



let ivsize = aeadRealIVSize AES_128_GCM
type keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
type cipher = b:bytes{B.length b >= ivsize}
type nonce = bytes
(* MK: minimal cipher length twice blocksize? *)

let ae_region_color = -1


private val ae_key_region: (r:MR.rid{extends r root /\ is_eternal_region r /\ (color r = ae_region_color) /\ is_below r root /\ disjoint r id_table_region})
private let ae_key_region = 
  recall_region id_table_region;
  new_colored_region root ae_region_color


type log_entry i = (protected_ae_plain i) * cipher * nonce
type log_t (i:ae_id) (r:rid) = m_rref r (seq (log_entry i)) grows

//type log_key = (cipher * nonce)
//type log_t (i:ae_id) = MM.t #ae_key_region 


val fresh_nonce: #(i:ae_id) -> (n:nonce) -> seq (log_entry i) -> Tot bool
let fresh_nonce #i n entries =
  not (Some? (seq_find (fun (_,_,n') -> n' = n) entries))

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions.
*)

noeq type key =
  | Key: #i:ae_id -> #(region:rid{extends region ae_key_region}) -> raw:aes_key -> log:log_t i region -> key

val get_index: k:key -> Tot (i:ae_id{i=k.i})
let get_index k = k.i


(**
    Safe_key_gen makes sure that memory safety is preserved while generating a key.
    Also, it makes sure that the log created along with the key is empty.
*)
let safe_key_gen parent m0 k m1 =
  // Reason about regions (HyperHeap)
  HH.modifies Set.empty m0.h m1.h
  /\ extends k.region parent
  /\ fresh_region k.region m0.h m1.h
  /\ color k.region = ae_region_color
  /\ is_below k.region ae_key_region
  // Reason about memory (HyperStack)
  /\ m_contains k.log m1
  /\ m_sel m1 k.log == createEmpty


(**
   This function generates a key in a fresh region of memory below the parent region.
   The postcondition ensures that the log is empty after creation.
*)
val keygen: i:ae_id -> ST (k:key{k.i=i})
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 -> 
    safe_key_gen ae_key_region h0 k h1
  ))
let keygen i =
  let rnd_k = random keysize in
  let region = new_colored_region ae_key_region ae_region_color in
  let log = alloc_mref_seq region createEmpty in
  Key #i #region rnd_k log


(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
val leak_key: k:key{(ae_dishonest k.i) \/ ~(b2t ae_ind_cca)} -> Tot aes_key 
let leak_key k =
  k.raw

(**
   The coerce function transforms a raw aes_key into an abstract key. The function is stateful,
   as we need to allocate space in memory for the key. The refinement type on the key makes sure that
   abstract keys created this way can not be honest.
*)
val coerce_key: i:ae_id{(ae_dishonest i) \/ ~(prf_odh)} -> aes_key -> ST (k:key{k.i=i})
  (requires (fun _ -> True))
  (ensures  (safe_key_gen ae_key_region))
let coerce_key i raw = 
  let region = new_colored_region ae_key_region ae_region_color in
  let log = alloc_mref_seq region createEmpty in
  Key #i #region raw log


(**
   safe_log_append makes sure that new entries added to the log are appended in a memory-safe way.
*)

//Ideally use this instead of every postcondition separately.
let safe_log_append k entry h0 h1 =
    let s1 = Set.singleton id_table_region in
    let s2 = Set.singleton k.region in
    let s = Set.union s1 s2 in
    modifies_just s h0.h h1.h
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == snoc (m_sel h0 k.log) entry
    /\ witnessed (at_least (Seq.length (m_sel h0 k.log)) entry k.log)


(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #(i:ae_id) -> n:nonce -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
  (requires (fun h0 -> 
    let entries = m_sel h0 k.log in
    fresh_nonce n entries
  ))
  (ensures  (fun h0 c h1 ->
    let s1 = Set.singleton id_table_region in
    let s2 = Set.singleton k.region in
    let s = Set.union s1 s2 in
    modifies_just s h0.h h1.h
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == snoc (m_sel h0 k.log) (m,c,n)
    /\ witnessed (at_least (Seq.length (m_sel h0 k.log)) (m,c,n) k.log)
    ))
let encrypt #i n k m =
  admit(); // REMOVE THIS!!!
  m_recall k.log;
  let iv = random ivsize in
  let ae_honest_i = ae_honestST i in
  let p = if (ae_ind_cca && ae_honest_i) then createBytes (length m) 0z else (repr m) in
  let c = CoreCrypto.aead_encrypt AES_128_GCM k.raw iv empty_bytes p in
  let c = iv@|c in
  write_at_end k.log (m,c,n);
  c


val is_in_entries: #i:ae_id -> log_entry i -> seq (log_entry i) -> Type0
let is_in_entries #i entry entries =
  Seq.contains entries entry
  

(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
   TODO: Make this a total function.
*)
val decrypt: #(i:ae_id) -> n:nonce -> k:key{k.i=i} -> c:cipher -> ST (option (protected_ae_plain i))
  (requires (fun h -> Map.contains h.h k.region))
  (ensures  (fun h0 res h1 -> 
    modifies_one id_table_region h0.h h1.h
    /\ ( (~(b2t ae_ind_cca) \/ ae_dishonest i) \/ ((b2t ae_ind_cca /\ ae_honest i /\ Some? res) ==> (is_in_entries (Some?.v res,c,n) (m_sel h0 k.log))))
    //Some? (seq_find (fun (res',c',n') -> c' = c && n' = n && res' = res) (m_sel h0 k.log)))
//      Seq.contains (Some?.v res,c,n) (m_sel h0 k.log))
    ))

//val find_in_entries: #i:ae_id -> log_entry i -> seq (log_entry i) -> Type0
//let find_in_entries #i entry entries =
  

let decrypt #i n k c =
  admit(); //REMOVE THIS !!! (You may have to find proper settings for Z3,
	   // but this has verified before.
  let ae_honest_i = ae_honestST i in
  if ae_ind_cca && ae_honest_i then (
    let log = m_read k.log in
    match Seq.find_l (fun (_,c',n') -> c' = c && n' = n) log with
    | Some (m,_,_) ->
      lemma_find_l_contains (fun (_,c',n') -> c' = c && n' = n) log;
      Some m
    | None -> None
  ) else (
    let iv,c' = split c ivsize in
    assume( B.length c' >= aeadTagSize AES_128_GCM);
    let poption = (CoreCrypto.aead_decrypt AES_128_GCM k.raw iv empty_bytes c') in
    match poption with
    | Some p -> Some (PlainAE.coerce #i (p))
    | None -> None
  )

//val dec_enc_inverse_lemma: #(i:ae_id) -> n:nonce -> k:key -> c:cipher -> ST bool
//  (requires (fun h0 -> 
//    k.i==i
//    /\ Map.contains h0.h k.region
//  ))
//  (ensures (fun h0 b h1 -> b))
//let dec_enc_inverse_lemma #i n k c =
//  match decrypt #i n k c with
//  | Some m' -> c = encrypt #i n k m'
//  | None -> true
    
