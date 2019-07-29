module Setoids.Crypto.ODH

open FStar.Bytes
open FStar.UInt32
open Setoids
open Setoids.Crypto
open Setoids.Crypto.KEY

module DM = FStar.DependentMap

let share (n:u32) = lbytes32 n
let exponent (n:u32) = lbytes32 n
assume val exponentiate : #n:u32 -> x:share n -> y:exponent n -> share n
assume val generator : n:u32 -> lbytes32 n

let odh_state n = Map.t (share n) (option (exponent n))

#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 3"
#set-options "--query_stats"
/// Key state relation could be hi here.
let gen_dh_t n =
  (lo unit)
  ^--> eff_rel (lo (odh_state n) ** lo (key_state n)) (lo (share n))
let gen_dh n : gen_dh_t n =
  fun _ ->
    combined_state  <-- get ;
    let odh_st = fst combined_state in
    let key_st = snd combined_state in
    x_exp <-- sample_multiple #(odh_state n * key_state n) n;
    let x = exponentiate (generator n) x_exp in
    let s':odh_state n = Map.upd odh_st x (Some x_exp) in
    put (s',key_st) ;;
    return x

/// The key_state relation should be `hi` here.
let odh_t n =
  (lo (share n) ** lo (share n))
  //^--> eff_rel (lo (odh_state n) ** hi (key_state n)) (lo handle)
  ^--> eff_rel (lo (odh_state n) ** lo (key_state n)) (lo handle)

#reset-options
#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 3"
#set-options "--query_stats"
let odh n (key_module:module_t (key_write_sig n)) : odh_t n =
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
      let k = exponentiate y x_exp in
      let k_set : key_set_t n = get_oracle key_module ID_SET in
      lift_right (k_set (h, k));;
      return h

type odh_labels =
  | GEN_DH
  | ODH

let odh_field_types n : odh_labels -> Type0 =
  function GEN_DH -> gen_dh_t n
         | ODH -> odh_t n

let odh_field_rels n : (l:odh_labels -> erel (odh_field_types n l)) =
  function GEN_DH -> fun _ _ -> True
           //arrow
           //  (lo unit)
           //  (eff_rel (lo (odh_state n) ** lo (key_state n)) (lo (share n)))
         | ODH -> fun _ _ -> True
           //arrow
           //  (lo (share n) ** lo (share n))
           //  (eff_rel (lo (odh_state n) ** lo (key_state n)) (lo handle))

let odh_sig (n:u32) = {
  labels = odh_labels;
  ops = odh_field_types n;
  rels = odh_field_rels n
  }

let odh_module (n:u32) (km:module_t (key_write_sig n)) : module_t (odh_sig n) =
  DM.create #_ #(odh_sig n).ops
    (function GEN_DH -> gen_dh n
            | ODH -> odh n km)

let odh_functor n
  : functor_t (key_write_sig n) (odh_sig n)
  = fun (k:module_t (key_write_sig n)) -> odh_module n k

let odh_composition n
  : functor_t (key_sig n) (sig_prod (odh_sig n) (key_read_sig n)) =
  functor_prod_shared_sig
    (key_sig n)
    (odh_sig n)
    (key_read_sig n)
    (comp (odh_functor n) (key_write_functor n))
    (key_read_functor n)

let odh0_game (n:u32)
  : functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))
  =
  as_fun (odh_composition n (KEY.key0_module n))

let odh1_game (n:u32)
  : functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))
  =
  as_fun (odh_composition n (KEY.key1_module n))

let odh_adversary n aes = atk (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))

assume val odh_eps: n:u32 -> eps (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))

let odh_functor_rel n : per (functor_t (sig_unit) (sig_prod (odh_sig n) (key_read_sig n))) =
  fun funct_a funct_b -> True

/// Questions:
/// - What would a relation on a functor look like?
/// - How to instantiate a hypothesis?
let odh_assumption n = eq (odh_functor_rel n) (odh_eps n) (odh0_game n) (odh1_game n)
