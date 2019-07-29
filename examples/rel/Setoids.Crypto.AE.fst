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
/// Ideally, refine length of output bytes to be the relevant function of the input bytes. Maybe a lemma?
let enc_t (n:u32) (aes:ae_scheme n) =
  enc_inputs aes
    ^--> eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo bytes)

let enc0 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (enc_t n aes) =
  fun (p,nonce,h) ->
    combined_state <-- get ;
    let ae_st,k_st = combined_state in
    match DM.sel #ae_log_key #(ae_log_value aes) ae_st (h,nonce) with
    | Some option_map ->
      raise #(ae_log #n aes*key_state n)
    | None ->
      let k_get : key_get_t n = get_oracle key_module ID_GET in
      k <-- lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #((lo (key_state n))) #(key n) #(lo (key n)) (k_get h);
      let c = aes.enc p k nonce in
      let ae_st' = DM.upd ae_st (h,nonce) (Some (c,p)) in
      put (ae_st',k_st);;
      return c


#reset-options
#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 3"
#set-options "--query_stats"
let enc1 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (enc_t n aes) =
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
      return #(ae_log #n aes*key_state n) #(bytes) #(ae_log_rel #n aes ** (lo (key_state n))) #(lo bytes) c

let dec_inputs #n (aes:ae_scheme n) = triple_rel (lo (c:bytes{len c `lte` aes.ciphertext_length aes.max_plaintext_length})) (lo bytes) (lo handle)

let dec_t (n:u32) (aes:ae_scheme n) =
  dec_inputs aes
  ^--> eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length})))

let dec0 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (dec_t n aes) =
  fun (c,nonce,h) ->
  combined_state <-- get ;
  let ae_st,k_st = combined_state in
  let k_get : key_get_t n = get_oracle key_module ID_GET in
  k <-- lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #((lo (key_state n))) #(key n) #(lo (key n)) (k_get h);
  return #(combined_state_t #n aes) #_ #(ae_log_rel #n aes ** hi (key_state n)) #(lo (option (p:bytes{len p `lte` aes.max_plaintext_length}))) (aes.dec c k nonce)

let dec1 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (dec_t n aes) =
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

let ae_field_types n aes : ae_labels -> Type =
    function  ENC -> enc_t n aes
            | DEC -> dec_t n aes

// The relations seem to be the problem. I have removed the relations for now.
let ae_field_rels n aes : (l:ae_labels -> erel (ae_field_types n aes l)) =
  function
      ENC -> fun _ _ -> True //arrow (enc_inputs aes) (eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo bytes))
    | DEC -> fun _ _ -> True //arrow (dec_inputs aes) (eff_rel (ae_log_rel #n aes ** lo (key_state n)) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length}))))

let ae_sig (n:u32) (aes:ae_scheme n) = {
  labels = ae_labels;
  ops = ae_field_types n aes;
  rels = ae_field_rels n aes
  }

let ae0_module (n:u32) (aes:ae_scheme n) (k:module_t (key_read_sig n)) : module_t (ae_sig n aes) =
  DM.create #_ #(ae_sig n aes).ops
    (function ENC -> enc0 n aes k
            | DEC -> dec0 n aes k)

let ae1_module (n:u32) (aes:ae_scheme n) (k:module_t (key_read_sig n)) : module_t (ae_sig n aes) =
  DM.create #_ #(ae_sig n aes).ops
    (function ENC -> enc1 n aes k
            | DEC -> dec1 n aes k)

/// This doesn't cast to a functor properly
let ae0_functor (n:u32) (aes:ae_scheme n)
  : functor_t (key_read_sig n) (ae_sig n aes)
  = fun (k:module_t (key_read_sig n)) ->
    ae0_module n aes k

let ae1_functor (n:u32) (aes:ae_scheme n)
  : functor_t (key_read_sig n) (ae_sig n aes)
  = fun (k:module_t (key_read_sig n)) ->
    ae1_module n aes k

let ae0_composition n (aes:ae_scheme n)
  : functor_t (key_sig n) (sig_prod (key_write_sig n) (ae_sig n aes)) =
  functor_prod_shared_sig
    (key_sig n)
    (key_write_sig n)
    (ae_sig n aes)
    (key_write_functor n)
    (comp (ae0_functor n aes) (key_read_functor n))

let ae1_composition n (aes:ae_scheme n)
  : functor_t (key_sig n) (sig_prod (key_write_sig n) (ae_sig n aes)) =
  functor_prod_shared_sig
    (key_sig n)
    (key_write_sig n)
    (ae_sig n aes)
    (key_write_functor n)
    (comp (ae1_functor n aes) (key_read_functor n))

module KEY = Setoids.Crypto.KEY

let ae_game0 n (aes:ae_scheme n)
  : functor_t (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))
  =
  as_fun (ae0_composition n aes (KEY.key1_module n))

let ae_game1 n (aes:ae_scheme n)
  : functor_t (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))
  =
  as_fun (ae1_composition n aes (KEY.key1_module n))

let ae_adversary n aes = atk (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))

assume val ae_eps: n:u32 -> aes:ae_scheme n -> eps (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))

let ae_functor_rel n aes : per (functor_t (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))) =
  fun funct_a funct_b -> True

/// Questions:
/// - What would a relation on a functor look like?
/// - How to instantiate a hypothesis?
let ae_assumption n aes = eq (ae_functor_rel n aes) (ae_eps n aes) (ae_game0 n aes) (ae_game1 n aes)
