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

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
noeq type ae_scheme (n:u32) =
  | AES:
  max_plaintext_length: u32 ->
  ciphertext_length: (plaintext_length:u32{plaintext_length `lte` max_plaintext_length} -> u32) ->
  enc: (p:bytes -> k:key n -> nonce:bytes -> eff (lo unit ) (lo bytes)) ->
  dec: (c:bytes -> k:key n -> nonce:bytes -> option (p:bytes{len p `lte` max_plaintext_length})) ->
  ae_scheme n

/// Map from nonces to a maps from ciphertext to plaintexts
/// Should the state be dependent on the AE scheme?
let ae_log #n (aes:ae_scheme n) = plaintext_log aes.max_plaintext_length

let ae_log_rel (#n:u32) (aes:ae_scheme n) = lo (ae_log aes)

let combined_state_t n aes = ae_log #n aes * key_state n
let combined_state_rel n aes = lo (ae_log #n aes) ** lo (key_state n)

let enc_inputs n (aes:ae_scheme n) =
  triple_rel
    (lo (p:bytes{len p `lte` aes.max_plaintext_length}))
    (lo bytes)
    (lo handle)


#set-options "--z3rlimit 350 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
val get_related (n:u32)
                (aes:ae_scheme n)
                (a0 a1:type_of ((sig_rel (key_read_sig n)) ** enc_inputs n aes))
                (s0 s1:type_of (default_tape_rel ** combined_state_rel n aes))
                (h0 h1:type_of (lo handle))
  : Lemma
      (requires
        a0 `((sig_rel (key_read_sig n)) ** enc_inputs n aes)` a1 /\
        s0 `(default_tape_rel ** combined_state_rel n aes)` s1 /\
        h0 `lo handle` h1)

      (ensures (
        let g0 : key_get_t n = get_oracle ID_GET (fst a0) in
        let g1 : key_get_t n = get_oracle ID_GET (fst a1) in
        let g00 : eff (combined_state_rel n aes) (lo (key n)) = lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #(key_state_rel n) (g0 h0 <: eff (key_state_rel n) (lo (key n))) in
        let g11 : eff (combined_state_rel n aes) (lo (key n)) = lift_right #(ae_log #n aes) #(ae_log_rel #n aes) #(key_state n) #(key_state_rel n) (g1 h1 <: eff (key_state_rel n) (lo (key n))) in
        g00 s0 == g11 s1))
let get_related n aes a0 a1 s0 s1 h0 h1 =
    let g0 : key_get_t n = get_oracle ID_GET (fst a0) in
    let g1 : key_get_t n = get_oracle ID_GET (fst a1) in
    assert (g0 h0 (fst s0, (snd (snd s0))) `(triple_rel (option_rel (lo (key n))) (key_state_rel n) default_index_rel)` g1 h1 (fst s0, snd (snd s1)))

/// Ideally, refine length of output bytes to be the relevant function of the input bytes. Maybe a lemma?
let enc_t_base (n:u32) (aes:ae_scheme n) =
  ((sig_rel (key_read_sig n)) ** enc_inputs n aes)
    ^^--> eff_rel (combined_state_rel n aes) (lo bytes)

let enc_t (n:u32) (aes:ae_scheme n) =
  ((sig_rel (key_read_sig n)) ** enc_inputs n aes)
    ^--> eff_rel (combined_state_rel n aes) (lo bytes)

let enc0' (n:u32) (aes:ae_scheme n) : (enc_t_base n aes) =
  fun (key_module, (p,nonce,h)) ->
    combined_state <-- get ;
    let ae_st,k_st = combined_state in
    match DM.sel #plaintext_log_key #(plaintext_log_value aes.max_plaintext_length) ae_st (h,nonce) with
    | Some option_map ->
      raise #(ae_log #n aes*key_state n)
    | None ->
      let k_get : key_get_t n = get_oracle ID_GET key_module in
      k <-- lift_right (k_get h);
      c <-- lift_tape (aes.enc p k nonce);
      let ae_st' = DM.upd ae_st (h,nonce) (Some (c,p)) in
      put (ae_st',k_st);;
      return c

#set-options "--z3rlimit 1050 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --query_stats"
let enc0 (n:u32) (aes:ae_scheme n) : (enc_t n aes) =
  let aux (a0 a1:type_of ((sig_rel (key_read_sig n)) ** enc_inputs n aes))
          (s0 s1:type_of (default_tape_rel ** combined_state_rel n aes))
          (x0 x1:type_of (lo handle))
  : Lemma
      (requires
        a0 `((sig_rel (key_read_sig n)) ** enc_inputs n aes)` a1 /\
        s0 `(default_tape_rel ** (combined_state_rel n aes))` s1 /\
        x0 `(enc_inputs n aes)` x1
        )
      (ensures
        (enc0' n aes a0 s0 `(triple_rel (option_rel (lo (bytes))) (combined_state_rel n aes) default_index_rel)`
         enc0' n aes a1 s1))
     [SMTPat (enc0' a0 s0);
      SMTPat (enc0' a1 s1)]
  =
    admit();
    get_related n aes a0 a1 s0 s1 x0 x1
 in
 admit();
 enc0' n aes


let enc1 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (enc_t n aes) =
  fun (p,nonce,h) ->
    combined_state <-- get ;
    let ae_st,k_st : combined_state_t n aes = combined_state in
    match DM.sel #plaintext_log_key #(plaintext_log_value aes.max_plaintext_length) ae_st (h,nonce) with
    | Some option_map -> // Nonce is not unique
      raise
    | None ->
      c <-- sample_multiple (aes.ciphertext_length (len p));
      let ae_st' = DM.upd ae_st (h,nonce) (Some (c,p)) in
      put (ae_st',k_st);;
      return #_ #(bytes) c

let dec_inputs n (aes:ae_scheme n) =
  triple_rel
    (lo (c:bytes{len c `lte` aes.ciphertext_length aes.max_plaintext_length}))
    (lo bytes)
    (lo handle)

let dec_t (n:u32) (aes:ae_scheme n) =
  dec_inputs n aes
    ^--> eff_rel (combined_state_rel n aes) (option_rel (lo (p:bytes{len p `lte` aes.max_plaintext_length})))

let dec0 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (dec_t n aes) =
  fun (c,nonce,h) ->
    combined_state <-- get ;
    let ae_st,k_st = combined_state in
    let k_get : key_get_t n = get_oracle key_module ID_GET in
    k <-- lift_right (k_get h);
    let option_p = aes.dec c k nonce in
    return option_p

let dec1 (n:u32) (aes:ae_scheme n) (key_module:module_t (key_read_sig n)) : (dec_t n aes) =
  fun (c,nonce,h) ->
    combined_state <-- get ;
    let ae_st,k_st : combined_state_t n aes = combined_state in
    match DM.sel ae_st (h,nonce) with
    | Some (c',p) -> // Nonce is not unique
      if c = c' then
        return (Some p)
      else
        return None
    | None ->
      return None

type ae_labels =
    | ENC
    | DEC

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let ae_field_types n aes : ae_labels -> Type =
    function  ENC -> enc_t n aes
            | DEC -> dec_t n aes

let ae_field_rels n aes : (l:ae_labels -> erel (ae_field_types n aes l)) =
  function
      ENC ->
        arrow
          (enc_inputs n aes)
          (eff_rel (combined_state_rel n aes) (lo bytes))
    | DEC ->
        arrow
          (dec_inputs n aes)
          (eff_rel (combined_state_rel n aes) (option_rel (lo (p:bytes{len p `lte` aes.max_plaintext_length}))))

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
      admit()
      //ae0_module n aes k

let ae1_functor (n:u32) (aes:ae_scheme n)
  : functor_t (key_read_sig n) (ae_sig n aes)
  = fun (k:module_t (key_read_sig n)) ->
      ae1_module n aes k

let ae0_composition n (aes:ae_scheme n)
  : functor_t (key_sig n) (sig_prod (key_write_sig n) (ae_sig n aes)) =
  functor_prod_shared_sig
    (key_write_functor n)
    (comp (ae0_functor n aes) (key_read_functor n))

let ae1_composition n (aes:ae_scheme n)
  : functor_t (key_sig n) (sig_prod (key_write_sig n) (ae_sig n aes)) =
  functor_prod_shared_sig
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

let ae_rel n aes : per (functor_t (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes)))  = fun (ae0:functor_t (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))) (ae1:functor_t (sig_unit) (sig_prod (key_write_sig n) (ae_sig n aes))) ->
  let ae0_module = ae0 mod_unit in
  let ae1_module = ae1 mod_unit in
  sig_rel' (sig_prod (key_write_sig n) (ae_sig n aes)) ae0_module ae1_module

assume val ae_assumption : n:u32 -> aes:ae_scheme n -> eq (ae_rel n aes) (ae_eps n aes) (ae_game0 n aes) (ae_game1 n aes)
