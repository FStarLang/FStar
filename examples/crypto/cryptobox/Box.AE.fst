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


assume val aead_decryptT:
  a: aead_cipher -> 
  k: lbytes (aeadKeySize a) -> 
  iv:lbytes (aeadRealIVSize a) -> 
  ad:bytes -> 
  ciph:bytes{B.length ciph >= aeadTagSize a} -> 
  GTot (o:option (b:bytes{B.length b + aeadTagSize a = B.length ciph}))
  
assume val aead_decrypt:
  a: aead_cipher -> 
  k: lbytes (aeadKeySize a) -> 
  iv:lbytes (aeadRealIVSize a) -> 
  ad:bytes -> 
  ciph:bytes{B.length ciph >= aeadTagSize a} -> 
  EXT (o:option (b:bytes{B.length b + aeadTagSize a = B.length ciph})
    {(forall (p:bytes). ciph = aead_encryptT a k iv ad p <==> (Some? o /\ Some?.v o == p))
    /\ o = aead_decryptT a k iv ad ciph })


type noncesize = aeadRealIVSize AES_128_CCM
type keysize = aeadKeySize AES_128_CCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
type cipher = b:bytes
type nonce = B.lbytes noncesize


let ae_region_color = -1


private val ae_key_region: (r:MR.rid{extends r root /\ is_eternal_region r /\ (color r = ae_region_color) /\ is_below r root /\ disjoint r id_table_region})
private let ae_key_region = 
  recall_region id_table_region;
  new_colored_region root ae_region_color


//type log_entry i = (protected_ae_plain i) * cipher * nonce
//type log_t (i:ae_id) (r:rid) = m_rref r (seq (log_entry i)) grows

type log_key = nonce
type log_value (i:ae_id) = (cipher*protected_ae_plain i)
type log_range = fun (i:ae_id) -> (fun log_key -> (log_value i))
type log_inv (i:ae_id) (f:MM.map' log_key (log_range i)) = True
type log_t (i:ae_id) (r:rid)  = MM.t r log_key (log_range i) (log_inv i)




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
  /\ m_sel m1 k.log == MM.empty_map log_key (log_range k.i)


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
  let log = MM.alloc #region #log_key #(log_range i) #(log_inv i) in
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
  let log = MM.alloc #region #log_key #(log_range i) #(log_inv i) in
  Key #i #region raw log


(**
   safe_log_append makes sure that new entries added to the log are appended in a memory-safe way.
*)

#set-options "--initial_fuel 100 --initial_ifuel 100"
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #(i:ae_id) -> n:nonce -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
  (requires (fun h0 -> 
    MM.fresh k.log n h0
    /\ ae_fixed i
  ))
  (ensures  (fun h0 c h1 ->
    modifies_one k.region h0.h h1.h
    /\ m_contains k.log h1
    /\ (
	( (ae_dishonest i \/ ~(b2t ae_ind_cca))
	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k.raw n empty_bytes (repr m))
      \/ 
        ( (ae_honest i /\ b2t ae_ind_cca)
	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k.raw n empty_bytes (createBytes (length m) 0z) )
      )
    /\ (ae_dishonest i \/ ae_honest i)
    /\ MR.witnessed (MM.contains k.log n (c,m))
    ))
let encrypt #i n k m =
  m_recall k.log;
  let ae_honest_i = ae_honestST i in
  let p = 
    if (ae_ind_cca && ae_honest_i) then 
      createBytes (length m) 0z 
    else 
      repr m 
  in
  let c = CoreCrypto.aead_encrypt AES_128_CCM k.raw n empty_bytes p in
  MR.m_recall k.log;
  MM.extend k.log n (c,m);
  c
#reset-options

#set-options "--z3rlimit 100 --initial_fuel 3 --initial_ifuel 1"
(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
val decrypt: #(i:ae_id) -> n:nonce -> k:key{k.i=i} -> c:cipher{B.length c >= aeadTagSize AES_128_CCM} -> ST (option (protected_ae_plain i))
  (requires (fun h -> 
    Map.contains h.h k.region
    /\ ae_fixed i
  ))
  (ensures  (fun h0 res h1 -> 
    modifies_none h0 h1
    /\ m_contains k.log h1
    /\ (
        ((~(b2t ae_ind_cca) \/ ae_dishonest i) 
        	==> (Some? (aead_decryptT AES_128_CCM k.raw n empty_bytes c) 
        	  ==> Some? res /\ Some?.v res == coerce (Some?.v (aead_decryptT AES_128_CCM k.raw n empty_bytes c))))
      \/
        (( (b2t ae_ind_cca) /\ ae_honest i ) 
        	==> (MM.defined k.log n h0 /\ (fst (MM.value k.log n h0) == c ) 
        	  ==> Some? res /\ Some?.v res == snd (MM.value k.log n h0)))
        )
  ))
let decrypt #i n k c =
  let ae_honest_i = ae_honestST i in
  m_recall k.log;
  if ae_ind_cca && ae_honest_i then
    match MM.lookup k.log n with
    | Some (c',m') -> 
      if c' = c then 
	Some m'
      else 
	None
    | None -> None
  else 
    let poption = (aead_decrypt AES_128_CCM k.raw n empty_bytes c) in
    match poption with
    | Some p -> Some (PlainAE.coerce #i p)
    | None -> None
  

#reset-options


val dec_enc_inverse_lemma: #(i:ae_id) -> n:nonce -> k:key -> c:cipher{B.length c >= aeadTagSize AES_128_CCM} -> ST bool
  (requires (fun h0 -> 
    k.i==i
    /\ Map.contains h0.h k.region
    /\ ae_fixed i
    /\ MM.fresh k.log n h0
  ))
  (ensures (fun h0 b h1 -> b
  ))
let dec_enc_inverse_lemma #i n k c =
  match decrypt #i n k c with
  | Some m' -> c = encrypt #i n k m'
  | None -> true
    
