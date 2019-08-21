module Setoids.Crypto.ODH

open FStar.Bytes
open FStar.UInt32
open Setoids
open Setoids.Crypto
open Setoids.Crypto.KEY

module DM = FStar.DependentMap

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
let share (n:u32) = lbytes32 n
let exponent (n:u32) = lbytes32 n

noeq
type odh_scheme (n:u32) =
  | OS:
  exponentiate: (x:share n -> y:exponent n -> share n) ->
  generator: share n ->
  generate_exponent: (eff (lo unit) (lo (exponent n))) ->
  odh_scheme n

abstract let odh_state n = Map.t (share n) (option (exponent n))

let gen_dh_t n =
  (lo unit)
    ^--> eff_rel (lo (odh_state n) ** lo (key_state n)) (lo (share n))
let gen_dh n (os:odh_scheme n) : gen_dh_t n =
  fun _ ->
    combined_state  <-- get ;
    let odh_st = fst combined_state in
    let key_st = snd combined_state in
    x_exp <-- lift_tape #_ #(lo (odh_state n) ** lo (key_state n)) #_ #(lo (exponent n)) os.generate_exponent;
    let x = os.exponentiate os.generator x_exp in
    let s':odh_state n = Map.upd odh_st x (Some x_exp) in
    put (s',key_st) ;;
    return x

let odh_t n =
  (lo (share n) ** lo (share n))
    ^--> eff_rel (lo (odh_state n) ** lo (key_state n)) (lo handle)

let odh n (os:odh_scheme n) (key_module:module_t (key_write_sig n)) : odh_t n =
  fun (x,y) ->
    combined_state  <-- get ;
    let odh_st = fst combined_state in
    match Map.sel odh_st x with
    | None ->
      raise
    | Some x_exp ->
      let h =
        if int_of_bytes x <= int_of_bytes y then
          (x,y)
        else
          (y,x)
      in
      let k = os.exponentiate y x_exp in
      let k_set : key_set_t n = get_oracle key_module ID_SET in
      lift_right (k_set (h, k));;
      return h

type odh_labels =
  | GEN_DH
  | ODH

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let odh_field_types n : odh_labels -> Type0 =
  function GEN_DH -> gen_dh_t n
         | ODH -> odh_t n

let odh_field_rels n : (l:odh_labels -> erel (odh_field_types n l)) =
  function GEN_DH ->
           arrow
             (lo unit)
             (eff_rel (lo (odh_state n) ** lo (key_state n)) (lo (share n)))
         | ODH ->
           arrow
             (lo (share n) ** lo (share n))
             (eff_rel (lo (odh_state n) ** lo (key_state n)) (lo handle))

let odh_sig (n:u32) = {
    labels = odh_labels;
    ops = odh_field_types n;
    rels = odh_field_rels n
  }

let odh_module (n:u32) (os:odh_scheme n) (km:module_t (key_write_sig n)) : module_t (odh_sig n) =
  DM.create #_ #(odh_sig n).ops
    (function GEN_DH -> gen_dh n os
            | ODH -> odh n os km)

let odh_functor n (os:odh_scheme n)
  : functor_t (key_write_sig n) (odh_sig n)
  = fun (k:module_t (key_write_sig n)) ->
    admit()
    //odh_module n os k

let odh_composition n os
  : functor_t (key_sig n) (sig_prod (odh_sig n) (key_read_sig n))
  = functor_prod_shared_sig
    (comp (odh_functor n os) (key_write_functor n))
    (key_read_functor n)

let odh_game0 (n:u32) os
  : functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))
  = as_fun (odh_composition n os (KEY.key0_module n))

let odh_game1 (n:u32) os
  : functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))
  = as_fun (odh_composition n os (KEY.key1_module n))

let odh_adversary n = atk (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))

assume val odh_eps: n:u32 -> eps (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))

let odh_rel n : per (functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n)))  = fun (odh0:functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))) (odh1:functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))) ->
  let odh0_module = odh0 mod_unit in
  let odh1_module = odh1 mod_unit in
  sig_rel' (sig_prod (odh_sig n) (key_read_sig n)) odh0_module odh1_module

assume val odh_assumption : n:u32 -> os:odh_scheme n -> eq (odh_rel n) (odh_eps n) (odh_game0 n os) (odh_game1 n os)
