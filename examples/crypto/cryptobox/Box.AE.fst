module Box.AE

open FStar.Set
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
assume val ae_key_region: (r:MR.rid{ extends r root 
				     /\ is_eternal_region r 
				     /\ is_below r root
				     /\ disjoint r id_freshness_table_region
				     /\ disjoint r id_honesty_table_region
				     })

type log_key = nonce
type log_value (i:id{AE_id? i}) = (cipher*protected_ae_plain i)
type log_range = fun (i:id{AE_id? i}) -> (fun log_key -> (log_value i))
type log_inv (i:id{AE_id? i}) (f:MM.map' log_key (log_range i)) = True
type log_t (i:id{AE_id? i}) (r:rid)  = MM.t r log_key (log_range i) (log_inv i)


(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions.
*)
noeq abstract type key =
  | Key: #i:id{AE_id? i /\ unfresh i /\ registered i} -> #(region:rid{extends region ae_key_region /\ is_below region ae_key_region /\ is_eternal_region region}) -> raw:aes_key -> log:log_t i region -> key

val get_index: k:key -> Tot (i:id{i=k.i /\ unfresh i})
let get_index k = k.i

(**
   This function generates a key in a fresh region of memory below the parent region.
   The postcondition ensures that the log is empty after creation.
*)
val keygen: i:id{AE_id? i} -> ST (k:key{k.i=i})
  (requires (fun h -> 
    fresh i h // Prevents multiple keys with the same id
    /\ registered i // We require this to enforce a static corruption model.
  ))
  (ensures  (fun h0 k h1 -> 
    let (s:Set.set (HH.rid)) = Set.union (Set.singleton k.region) (Set.singleton id_freshness_table_region) in
    HH.modifies_just s h0.h h1.h
    /\ extends k.region ae_key_region
    /\ fresh_region k.region h0.h h1.h
    /\ is_below k.region ae_key_region
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == MM.empty_map log_key (log_range k.i)
    /\ unfresh i
    /\ ~(fresh i h1)
  ))
let keygen i =
  make_unfresh i;
  //ae_make_honest i;
  let rnd_k = random keysize in
  let region = new_region ae_key_region in
  let log = MM.alloc #region #log_key #(log_range i) #(log_inv i) in
  fresh_unfresh_contradiction i;
  Key #i #region rnd_k log

#set-options "--z3rlimit 20"
(**
   The coerce function transforms a raw aes_key into an abstract key. The function is stateful,
   as we need to allocate space in memory for the key. The refinement type on the key makes sure that
   abstract keys created this way can not be honest.
*)
val coerce_key: i:id{AE_id? i /\ (dishonest i)} -> raw_k:aes_key -> ST (k:key{k.i=i /\ k.raw = raw_k})
  (requires (fun h0 -> 
    registered i
  ))
  (ensures  (fun h0 k h1 ->
    let (s:Set.set (HH.rid)) = Set.union (Set.singleton k.region) (Set.singleton id_freshness_table_region) in
    HH.modifies_just s h0.h h1.h
    /\ extends k.region ae_key_region
    /\ fresh_region k.region h0.h h1.h
    /\ is_below k.region ae_key_region
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == MM.empty_map log_key (log_range k.i)
    /\ unfresh i
    /\ ~(fresh i h1)
    /\ (forall (k:AE.key). let i = AE.get_index k in ~( fresh i h1))
    /\ (forall (i:id). ~(fresh i h0) ==> ~(fresh i h1))
    /\ registered i
    /\ dishonest i
  ))
let coerce_key i raw = 
  make_unfresh i;
  let region = new_region ae_key_region in
  let log = MM.alloc #region #log_key #(log_range i) #(log_inv i) in
  fresh_unfresh_contradiction i;
  Key #i #region raw log
#reset-options


(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
val leak_key: k:key{(dishonest k.i) \/ ~(b2t ae_ind_cca)} -> Tot (raw_k:aes_key{raw_k=k.raw})
let leak_key k =
  k.raw

val get_keyGT: k:key -> GTot (raw_k:aes_key{raw_k=k.raw})
let get_keyGT k =
  k.raw

val get_logGT: k:key -> GTot (log:log_t k.i k.region{log=k.log})
let get_logGT k =
  k.log

val empty_log: i:id{AE_id? i} -> Tot (MM.map' log_key (log_range i))
let empty_log i = MM.empty_map log_key (log_range i)

val recall_log: k:key -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains k.log h1
  ))
let recall_log k =
  MR.m_recall k.log

val get_regionGT: k:key -> GTot (region:rid{region=k.region})
let get_regionGT k =
  k.region


#set-options "--z3rlimit 15"
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #(i:id{AE_id? i}) -> n:nonce -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
  (requires (fun h0 -> 
    MM.fresh k.log n h0
    /\ MR.m_contains k.log h0
    /\ registered i
  ))
  (ensures  (fun h0 c h1 ->
    let current_log = MR.m_sel h0 k.log in
    modifies_one k.region h0.h h1.h

    ///\ m_contains k.log h1
    /\ (
	( (dishonest i \/ ~(b2t ae_ind_cca))
	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k.raw n empty_bytes (repr m))
      \/ 
        ( (honest i /\ b2t ae_ind_cca)
	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k.raw n empty_bytes (createBytes (length m) 0z) )
      )
    /\ (dishonest i \/ honest i)
    /\ MR.witnessed (MM.contains k.log n (c,m))
    /\ MR.m_sel h1 k.log == MM.upd current_log n (c,m)
    ))
let encrypt #i n k m =
  let honest_i = is_honest i in
  let p = 
    if (ae_ind_cca && honest_i) then (
      createBytes (length m) 0z 
    ) else (
      repr m )
  in
  let c = CoreCrypto.aead_encrypt AES_128_CCM k.raw n empty_bytes p in
  MM.extend k.log n (c,m);
  c


(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
val decrypt: #(i:id{AE_id? i}) -> n:nonce -> k:key{k.i=i} -> c:cipher{B.length c >= aeadTagSize AES_128_CCM} -> ST (option (protected_ae_plain i))
  (requires (fun h -> 
    Map.contains h.h k.region
    /\ MR.m_contains k.log h
    /\ registered i
  ))
  (ensures  (fun h0 res h1 -> 
    modifies_none h0 h1
    /\ m_contains k.log h1
    /\ (
        ((~(b2t ae_ind_cca) \/ dishonest i) 
        	==> (Some? (aead_decryptT AES_128_CCM k.raw n empty_bytes c) 
        	     ==> Some? res /\ Some?.v res == coerce (Some?.v (aead_decryptT AES_128_CCM k.raw n empty_bytes c))))
      \/
        (( (b2t ae_ind_cca) /\ honest i /\ Some? res) 
        	==> (MM.defined k.log n h0 /\ (fst (MM.value k.log n h0) == c ) 
        	  /\ Some?.v res == snd (MM.value k.log n h0)))
        )
  ))
let decrypt #i n k c =
  let honest_i = is_honest i in
  if ae_ind_cca && honest_i then
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
