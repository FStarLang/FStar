module Box.AE

open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef

open Box.Flags
open Box.Indexing

open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes

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

type log_key = nonce
type log_value (i:eqtype) = (cipher*protected_ae_plain i)
type log_range = fun (i:eqtype) -> (fun log_key -> (log_value i))
type log_inv (i:eqtype) (f:MM.map' log_key (log_range i)) = True
type log_t (i:eqtype) (r:rid)  = MM.t r log_key (log_range i) (log_inv i)

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions.
*)
noeq type key (k_id_type:eqtype) =
  | Key: #i:k_id_type -> #(region:rid{extends region ae_key_region}) -> raw:aes_key -> log:log_t i region -> key

val get_index: k:key -> Tot (i:ae_id{i=k.i})
let get_index k = k.i


(**
    Safe_key_gen makes sure that memory safety is preserved while generating a key.
    Also, it makes sure that the log created along with the key is empty.
*)
let safe_key_gen parent m0 k m1 =
    modifies Set.empty m0 m1
  /\ extends k.region parent
  /\ fresh_region k.region m0.h m1.h
  /\ m_contains k.log m1
  /\ m_sel m1 k.log == createEmpty

noeq type ae_scheme =
  | AE_scheme: ae_is:id_scheme ->
	       ae_playin_scheme:plain_scheme ->
	       payload_plain_scheme:plain_scheme ->
	       keygen: (i:ae_is.id_type -> ST (k:key{k.i=i})
	         (requires (fun h0 -> True))
		 (ensures (fun h0 k h1 -> 
		   safe_key_gen ae_key_region h0 k h1
		 ))
	       ) ->
	       leak_key: (k:key{ae_is.dishonest k.i \/ ~(b2t ae_ind_cca)} -> aes_key) ->
	       coerce_key: (i:ae_is.id_type{(ae_is.dishonest i) \/ ~(prf_odh)} -> aes_key -> ST (k:key{k.i=i})
	         (requires (fun h0 -> True))
		 (ensures (fun h0 k h1 -> 
		   safe_key_gen ae_key_region h0 k h1
		 ))
	       ) ->
	       encrypt: (#(i:ae_is.id_Type) -> n:nonce -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
	         (requires (fun h0 -> 
		   MM.fresh k.log n h0
		   /\ ae_is.fixed i
		 ))
		 (ensures  (fun h0 c h1 ->
		   modifies_one k.region h0.h h1.h
		   /\ m_contains k.log h1
		   /\ (
		     ( (ae_is.dishonest i \/ ~(b2t ae_ind_cca))
		         ==> c = CoreCrypto.aead_encryptT AES_128_CCM k.raw n empty_bytes (repr m))
		     \/ 
		     ( (ae_is.honest i /\ b2t ae_ind_cca)
		         ==> c = CoreCrypto.aead_encryptT AES_128_CCM k.raw n empty_bytes (createBytes (length m) 0z) )
		     )
		   /\ (ae_is.dishonest i \/ ae_honest i)
		   /\ MR.witnessed (MM.contains k.log n (c,m))
		   ))
	       ) ->
	       decrypt: (#(i:ae_is.id_type) -> n:nonce -> k:key{k.i=i} -> c:cipher{B.length c >= aeadTagSize AES_128_CCM} -> ST (option (protected_ae_plain i))
	         (requires (fun h -> 
		   Map.contains h.h k.region
		   /\ ae_is.fixed i
		 ))
		 (ensures  (fun h0 res h1 -> 
		   modifies_none h0 h1
		   /\ m_contains k.log h1
		   /\ (
		     ( (ae_is.dishonest i \/ ~(b2t ae_ind_cca)) 
        	         ==> (Some? (aead_decryptT AES_128_CCM k.raw n empty_bytes c) 
        		   ==> Some? res /\ Some?.v res == coerce (Some?.v (aead_decryptT AES_128_CCM k.raw n empty_bytes c))))
		     \/
		     ( (ae_is.honest i /\ b2t ae_ind_cca)
        	         ==> (MM.defined k.log n h0 /\ (fst (MM.value k.log n h0) == c ) 
        		   ==> Some? res /\ Some?.v res == snd (MM.value k.log n h0)))
		     )
		 ))
	       ) ->
	       ae_scheme

let dh_spawn_instance (ae_is:)  =
(**
   This function generates a key in a fresh region of memory below the parent region.
   The postcondition ensures that the log is empty after creation.
*)
val keygen: i:ae_id -> parent:rid -> ST (k:key{k.i=i})
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 -> 
    safe_key_gen parent h0 k h1
  ))
let keygen i parent =
  let rnd_k = random keysize in
  let region = new_region parent in
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
val coerce_key: i:ae_id{(ae_dishonest i) \/ ~(prf_odh)} -> parent:rid -> aes_key -> ST (k:key{k.i=i})
  (requires (fun _ -> True))
  (ensures  (safe_key_gen parent))
let coerce_key i parent raw = 
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #i #region raw log

(**
   safe_log_append makes sure that new entries added to the log are appended in a memory-safe way.
*)
type safe_log_append k entry h0 h1 =
    modifies_one k.region h0 h1 
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == snoc (m_sel h0 k.log) entry
    /\ witnessed (at_least (Seq.length (m_sel h0 k.log)) entry k.log)


(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #(i:ae_id) -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
  (requires (fun h0 -> True
    (*m_contains k.log h0*)))
  (ensures  (fun h0 c h1 -> True 
//    /\ safe_log_append k (m,c) h0 h1 //add back once memory separation is fixed
    ))
let encrypt #i k m =
  m_recall k.log;
  let iv = random ivsize in
  //assert(ae_dishonest i \/ ae_honest i);
  let ae_honest_i = ae_honestST i in
  let p = if (ae_ind_cca && ae_honest_i) then createBytes (length m) 0z else (repr m) in
  let c = CoreCrypto.aead_encrypt AES_128_GCM k.raw iv empty_bytes p in
  let c = iv@|c in
  write_at_end k.log (m,c);
  c


(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
   TODO: Make this a total function.
*)
val decrypt: #(i:ae_id) -> k:key{k.i=i} -> c:cipher -> ST (option (protected_ae_plain i))
  (requires (fun h -> True (* Could require Map.contains h0 k.region *)))
  (ensures  (fun h0 res h1 -> True))
    (* Modifies_none h0 h1 *)
    (* /\ ( ( ae_ind_cca /\(ae_honest i)) ==> (get_index res) *)
    (* /\ ( (b2t ae_int_ctxt /\ honest i /\ Some? res) ==> Seq.mem (Some?.v res,c) (m_sel h0 k.log)  *)
    (* ))) *)
let decrypt #i k c =
  let ae_honest_i = ae_honestST i in
  if ae_ind_cca && ae_honest_i then
    let log = m_read k.log in
    match seq_find (fun mc -> snd mc = c) log with
    | Some mc -> Some (fst mc)
    | None -> None
  else
    let iv,c' = split c ivsize in
    assume( B.length c' >= aeadTagSize AES_128_GCM);
    let poption = (CoreCrypto.aead_decrypt AES_128_GCM k.raw iv empty_bytes c') in
//    admit ();
    match poption with
    | Some p -> Some (PlainAE.coerce #i (p))
    | None -> None
