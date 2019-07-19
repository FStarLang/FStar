module Setoids.Crypto.AE
open FStar.Bytes
open FStar.UInt32
open FStar.Map
open Setoids
open Setoids.Crypto
open Setoids.Crypto.KEY

module DM = FStar.DependentMap

////////////////////////////////////////////////////////////////////////////////
//AE package
////////////////////////////////////////////////////////////////////////////////

noeq type ae_scheme (n:u32) =
  | AES:
  max_plaintext_length: u32 ->
  ciphertext_length: (plaintext_length:u32{plaintext_length `lte` max_plaintext_length} -> u32) ->
  enc: (p:bytes -> k:key n -> nonce:bytes -> c:bytes) ->
  dec: (c:bytes -> k:key n -> nonce:bytes -> option (p:bytes{len p `lte` max_plaintext_length})) ->
  ae_scheme n

let ae_log_key = handle*bytes
let ae_log_value #n (aes:ae_scheme n) = fun (h,nonce) -> option (bytes*p:bytes{len p `lte` aes.max_plaintext_length})

/// Map from nonces to a maps from ciphertext to plaintexts
let ae_log #n (aes:ae_scheme n) =
  DM.t (handle*bytes) (ae_log_value aes)

let ae_log_rel (#n:u32) (aes:ae_scheme n) = lo (ae_log aes)

let combined_state_t #n aes = ae_log #n aes * key_state n

/// Is there a nicer way to have a function with mulitple inputs than using nested tuples?
/// How to use the 'secure information flow' relations again with AE^0 vs AE^1?
/// AE^0 also depends on the state of the key package.
/// Is there a way to improve verification performance and/or error messages?
/// Every AE function takes as additional parameter the module it is composed with.
/// AE Functor: Function from underlay module to AE sigu32ure

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 3"
/// This would be a nice, generic approach, but it's probably a little to complex
//let multi_rel' (tl:list Type) (rm:DMap.t (n:u32{n < List.Tot.length tl}) (fun i -> rel (List.Tot.index tl i))) (vm0 vm1:DMap.t (n:u32{n < List.Tot.length tl}) (fun i -> List.Tot.index tl i)) =
//  let logical_and t1 t2 = t1 /\ t2
//  let iterate_maps (i:u32{i < List.Tot.length tl}) =
//    let x0 = DMap.sel vm0 i in
//    let x1 = DMap.sel vm1 i in
//    let rel = DMap.sel rm i in
//    x0 `rel` x1
//  in
//  //let indices = mapi #Type (fun i _ -> i) tl in
//  let prop_list = List.Tot.mapi #Type (fun i _ -> iterate_maps i) tl in
//  admit()

let enc_inputs #n (aes:ae_scheme n) = triple_rel (lo (p:bytes{len p `lte` aes.max_plaintext_length})) (lo bytes) (lo handle)

#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 3"
let enc_0_t (n:u32) (aes:ae_scheme n) =
  enc_inputs aes
    ^--> eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo bytes)
let enc_1_t (n:u32) (aes:ae_scheme n) =
  enc_inputs aes
    ^--> eff_rel (ae_log_rel #n aes ** hi (key_state n)) (lo bytes)

let enc_0 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_sig n)) : (enc_0_t n aes) =
  fun (p,nonce,h) ->
    combined_state <-- get ;
    let ae_st,k_st = combined_state in
    match DM.sel #ae_log_key #(ae_log_value aes) ae_st (h,nonce) with
    | Some option_map ->
      raise #(ae_log #n aes*key_state n)
    | None ->
      let k_get : key_get_t n = get_oracle key_module GET in
      k <-- lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #(key_state_rel n) #(key n) #(lo (key n)) (k_get h);
      let c = aes.enc p k nonce in
      let ae_st' = DM.upd ae_st (h,nonce) (Some (c,p)) in
      put (ae_st',k_st);;
      return c


#reset-options
#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 3"
#set-options "--query_stats"
let enc_1 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_sig n)) : (enc_1_t n aes) =
  fun (p,nonce,h) ->
    combined_state <-- get ;
    let ae_st,k_st : ae_log aes*key_state n = combined_state in
    match DM.sel #ae_log_key #(ae_log_value aes) ae_st (h,nonce) with
    | Some option_map -> // Nonce is not unique
      raise
    | None ->
      c <-- sample_multiple (aes.ciphertext_length (len p));
      let ae_st' = DM.upd ae_st (h,nonce) (Some (c,p)) in
      put (ae_st',k_st);;
      return #(ae_log #n aes*key_state n) #(bytes) #(ae_log_rel #n aes ** key_state_rel n) #(lo bytes) c

let dec_inputs #n (aes:ae_scheme n) = triple_rel (lo (c:bytes{len c `lte` aes.ciphertext_length aes.max_plaintext_length})) (lo bytes) (lo handle)

let dec_0_t (n:u32) (aes:ae_scheme n) =
  dec_inputs aes
  ^--> eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length})))
let dec_1_t (n:u32) (aes:ae_scheme n) =
  dec_inputs aes
    ^--> eff_rel (ae_log_rel #n aes ** hi (key_state n)) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length})))

let dec_0 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_sig n)) : (dec_0_t n aes) =
  fun (c,nonce,h) ->
  combined_state <-- get ;
  let ae_st,k_st = combined_state in
  let k_get : key_get_t n = get_oracle key_module GET in
  k <-- lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #(key_state_rel n) #(key n) #(lo (key n)) (k_get h);
  return (aes.dec c k nonce)

let dec_1 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_sig n)) : (dec_1_t n aes) =
  fun (c,nonce,h) ->
  combined_state <-- get ;
  let ae_st,k_st : ae_log aes*key_state n = combined_state in
  match DM.sel ae_st (h,nonce) with
  | Some (c',p) -> // Nonce is not unique
    if c = c' then
      return #(combined_state_t #n aes) (Some p)
    else
      return None
  | None ->
    return #(combined_state_t #n aes) #_ #(ae_log_rel #n aes ** hi (key_state n)) #(lo (option (p:bytes{len p `lte` aes.max_plaintext_length}))) None

type ae_labels =
    | ENC
    | DEC

let ae0_field_types n aes : ae_labels -> Type =
    function  ENC -> enc_0_t n aes
            | DEC -> dec_0_t n aes

let ae1_field_types n aes : ae_labels -> Type =
    function  ENC -> enc_1_t n aes
            | DEC -> dec_1_t n aes

let ae0_field_rels n aes : (l:ae_labels -> erel (ae0_field_types n aes l)) =
  function
      ENC -> arrow (enc_inputs aes) (eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo bytes))
    | DEC -> arrow (dec_inputs aes) (eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length}))))

let ae1_field_rels n aes : (l:ae_labels -> erel (ae1_field_types n aes l)) =
  function
      ENC -> arrow (enc_inputs aes) (eff_rel (ae_log_rel #n aes ** hi (key_state n)) (lo bytes))
    | DEC -> arrow (dec_inputs aes) (eff_rel (ae_log_rel #n aes ** hi (key_state n)) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length}))))

let sig_ae0 (n:u32) (aes:ae_scheme n) = {
  labels = ae_labels;
  ops = ae0_field_types n aes;
  rels = ae0_field_rels n aes
  }

let sig_ae1 (n:u32) (aes:ae_scheme n) = {
  labels = ae_labels;
  ops = ae1_field_types n aes;
  rels = ae1_field_rels n aes
  }

let ae0_module (n:u32) (aes:ae_scheme n) (k:module_t (key_sig n)) : module_t (sig_ae0 n aes) =
  DM.create #_ #(sig_ae0 n aes).ops
    (function ENC -> enc_0 n aes k
            | DEC -> dec_0 n aes k)

let ae1_module (n:u32) (aes:ae_scheme n) (k:module_t (key_sig n)) : module_t (sig_ae1 n aes) =
  DM.create #_ #(sig_ae1 n aes).ops
    (function ENC -> enc_1 n aes k
            | DEC -> dec_1 n aes k)

/// This doesn't cast to a functor properly
let ae0_functor (n:u32) (aes:ae_scheme n)
  //: functor_t (key_sig n) (sig_ae0 n aes)
  = fun (k:module_t (key_sig n)) -> ae0_module n aes k

let ae1_functor (n:u32) (aes:ae_scheme n)
  : functor_t (key_sig n) (sig_ae1 n aes)
  = fun (k:module_t (key_sig n)) -> ae1_module n aes k

type id_ae_labels =
  | ID_SET
  | ID_CSET

let id_ae_field_types n : id_ae_labels -> Type0 =
    function ID_SET -> key_set_t n
           | ID_CSET -> key_cset_t n

let id_ae_field_rels n : (l:id_ae_labels -> erel (id_ae_field_types n l)) =
  function ID_SET -> arrow (lo handle ** lo (key n)) (eff_rel (key_state_rel n) (lo handle))
         | ID_CSET -> arrow (lo handle ** lo (key n)) (eff_rel (key_state_rel n) (lo handle))

let sig_id_ae (n:u32) = {
  labels = id_ae_labels;
  ops = id_ae_field_types n;
  rels = id_ae_field_rels n
  }

#set-options "--z3rlimit 350 --max_fuel 3 --max_ifuel 4"
let id_ae_module (n:u32) (km:module_t (key_sig n)) : module_t (sig_id_ae n) =
  DM.create #_ #(sig_id_ae n).ops
    (function ID_SET -> get_oracle km SET
            | ID_CSET -> get_oracle km CSET)

let id_ae_functor n
  : functor_t (key_sig n) (sig_id_ae n)
  = fun (k:module_t (key_sig n)) -> id_ae_module n k

//let ae_game0 n (aes:ae_scheme n) (km:module_t (key_sig n)) =
//  functor_prod
//    (key_sig n) (sig_id_gen n)
//    (key_sig n) (sig_ae0 n aes)
//    (id_ae_functor n)
//    (ae0_functor n aes)

let ae_game1 n (aes:ae_scheme n) (km:module_t (key_sig n)) =
  functor_prod
    (key_sig n) (sig_id_ae n)
    (key_sig n) (sig_ae1 n aes)
    (id_ae_functor n)
    (ae1_functor n aes)
