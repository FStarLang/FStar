module DPE2
open Pulse.Main
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open Pulse.Steel.Wrapper
module W = Pulse.Steel.Wrapper
module L = Steel.ST.SpinLock
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Array
open LinearScanHashTable
open PulseHashTable
module PHT = PulseHashTable
module LSHT = LinearScanHashTable
open HACL
open X509
open EngineTypes
open EngineCore
open L0Types
open L0Core
open Pulse.Class.BoundedIntegers
open DPE

(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table.
  NOTE: Returns 0 upon error
*)
```pulse
fn derive_child (sid:nat) (ctxt_hndl:nat) (record:record_t) (repr:repr_t)
  requires record_perm record repr
  returns _:nat
  ensures record_perm record repr
{
  let new_ctxt_hndl = prng ();

  let sht = dfst locked_sht;
  let sht_lk = dsnd locked_sht;
  W.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with spht. assert (models sht_sig sht spht);

  let opt_locked_cht = PHT.lookup #sht_sig #spht sht sid;

  match opt_locked_cht {
  Some locked_cht -> {
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    W.acquire #(ht_perm cht_sig cht) cht_lk;

    unfold (ht_perm cht_sig cht);
    with cpht0. assert (models cht_sig cht cpht0);

    let opt_locked_ctxt = PHT.lookup #cht_sig #cpht0 cht ctxt_hndl;

    match opt_locked_ctxt {
    Some locked_ctxt -> {
    let ctxt = dfst locked_ctxt;
    let ctxt_lk = dsnd locked_ctxt;
    W.acquire #(context_perm ctxt) ctxt_lk;

    match ctxt {
    Engine_context c -> {
      // NOTE: we won't eventually release engine_context_perm because we won't 
      // own it anymore -- we will disable the uds and free the uds array
      rewrite (context_perm ctxt) as (engine_context_perm c);
      unfold (engine_context_perm c);

      match record {
      Engine_record r -> {
        match repr {
        Engine_repr r0 -> {       
          rewrite (record_perm record repr) as (engine_record_perm r r0); 

          let cdi = new_array 0uy dice_digest_len;
          let ret = EngineCore.engine_main cdi c.uds r;
          with s. assert (A.pts_to cdi full_perm s);
          free_array c.uds;

          match ret {
          DICE_SUCCESS -> {
            let new_locked_context = init_l0_ctxt cdi;
            free_array cdi #(coerce dice_digest_len s);
            
            PHT.delete #cht_sig #cpht0 cht ctxt_hndl;
            with cpht1. assert (models cht_sig cht cpht1);
            let b = not_full #cht_sig #cpht1 cht;

            if b {
              PHT.insert #cht_sig #cpht1 cht new_ctxt_hndl new_locked_context; 

              rewrite (engine_record_perm r r0) as (record_perm record repr);
              fold (ht_perm sht_sig sht);
              fold (ht_perm cht_sig cht);
              W.release #(ht_perm sht_sig sht) sht_lk;
              W.release #(ht_perm cht_sig cht) cht_lk;

              new_ctxt_hndl
            } else {
              // ERROR -- table full
              rewrite (engine_record_perm r r0) as (record_perm record repr);
              fold (ht_perm sht_sig sht);
              fold (ht_perm cht_sig cht);
              W.release #(ht_perm sht_sig sht) sht_lk;
              W.release #(ht_perm cht_sig cht) cht_lk;

              new_ctxt_hndl
          }}
          DICE_ERROR -> {
            // ERROR -- DICE engine failed
            free_array cdi #(coerce dice_digest_len s);
            rewrite (engine_record_perm r r0) as (record_perm record repr);
            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;
            0
          }}}
        _ -> {
          // ERROR - repr should have type (Egnine_repr r0)
          zeroize_array uds_len c.uds #uds_bytes;
          disable_uds ();
          free_array c.uds;

          fold (ht_perm sht_sig sht);
          fold (ht_perm cht_sig cht);
          W.release #(ht_perm sht_sig sht) sht_lk;
          W.release #(ht_perm cht_sig cht) cht_lk;
          0
        }}
      }
      _ -> {
        // ERROR - record should have type (Engine_record r)
        zeroize_array uds_len c.uds;
        disable_uds ();
        free_array c.uds;

        fold (ht_perm sht_sig sht);
        fold (ht_perm cht_sig cht);
        W.release #(ht_perm sht_sig sht) sht_lk;
        W.release #(ht_perm cht_sig cht) cht_lk;
        0
      }}
    }
    L0_context c -> {
      // NOTE: we won't eventually release l0_context_perm because we won't 
      // own it anymore -- we will free the cdi array
      rewrite (context_perm ctxt) as (l0_context_perm c);
      unfold (l0_context_perm c);

      with s. assert (A.pts_to c.cdi full_perm s);

      match record {
      L0_record r -> {
        match repr {
        L0_repr r0 -> {
          let idcsr_ing = r.deviceIDCSR_ingredients;
          let akcrt_ing = r.aliasKeyCRT_ingredients;

          let deviceIDCRI_len = len_of_deviceIDCRI  idcsr_ing.version idcsr_ing.s_common 
                                                    idcsr_ing.s_org idcsr_ing.s_country;
          let aliasKeyTBS_len = len_of_aliasKeyTBS  akcrt_ing.serialNumber akcrt_ing.i_common 
                                                    akcrt_ing.i_org akcrt_ing.i_country 
                                                    akcrt_ing.s_common akcrt_ing.s_org 
                                                    akcrt_ing.s_country akcrt_ing.l0_version;
          let deviceIDCSR_len = length_of_deviceIDCSR deviceIDCRI_len;
          let aliasKeyCRT_len = length_of_aliasKeyCRT aliasKeyTBS_len;

          let deviceID_pub = new_array 0uy v32us;
          let deviceID_priv = new_array 0uy v32us;
          let aliasKey_pub = new_array 0uy v32us;
          let aliasKey_priv = new_array 0uy v32us;
          let deviceIDCSR = new_array 0uy deviceIDCSR_len;
          let aliasKeyCRT = new_array 0uy aliasKeyCRT_len;

          rewrite (record_perm record repr) as (l0_record_perm r r0); 

          assume_ (pure(valid_hkdf_ikm_len (digest_len dice_hash_alg)));
          
          L0Core.l0_main  c.cdi deviceID_pub deviceID_priv 
                          aliasKey_pub aliasKey_priv 
                          aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT 
                          deviceIDCRI_len deviceIDCSR_len deviceIDCSR r;
          free_array c.cdi;

          with (s1:elseq U8.t v32us). assert (A.pts_to aliasKey_priv full_perm s1);
          let new_locked_context = init_l1_ctxt deviceIDCSR_len aliasKeyCRT_len 
                                                deviceID_priv deviceID_pub
                                                aliasKey_priv aliasKey_pub 
                                                deviceIDCSR aliasKeyCRT;
          free_array deviceID_pub;
          free_array deviceID_priv;
          free_array aliasKey_pub;
          free_array aliasKey_priv;
          free_array deviceIDCSR;
          free_array aliasKeyCRT;
          
          PHT.delete #cht_sig #cpht0 cht ctxt_hndl;
          with cpht1. assert (models cht_sig cht cpht1);
          let b = not_full #cht_sig #cpht1 cht;

          if b {
            PHT.insert #cht_sig #cpht1 cht new_ctxt_hndl new_locked_context;

            rewrite (l0_record_perm r r0) as (record_perm record repr);

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;

            new_ctxt_hndl
          } else {
            // ERROR -- table full
            rewrite (l0_record_perm r r0) as (record_perm record repr);

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;

            new_ctxt_hndl
          }
        }
        _ -> {
          // ERROR - repr should have type (L0_repr r0)
          zeroize_array dice_digest_len c.cdi;
          free_array c.cdi;

          fold (ht_perm sht_sig sht);
          fold (ht_perm cht_sig cht);
          W.release #(ht_perm sht_sig sht) sht_lk;
          W.release #(ht_perm cht_sig cht) cht_lk;
          0
        }}
      }
      _ -> {
        // ERROR - record should have type (L0_record r)
        zeroize_array dice_digest_len c.cdi;
        free_array c.cdi;

        fold (ht_perm sht_sig sht);
        fold (ht_perm cht_sig cht);
        W.release #(ht_perm sht_sig sht) sht_lk;
        W.release #(ht_perm cht_sig cht) cht_lk;
        0
      }}
    }
    _ -> { 
      // ERROR - cannot invoke DeriveChild with L1 context
      fold (ht_perm sht_sig sht);
      fold (ht_perm cht_sig cht);
      W.release #(context_perm ctxt) ctxt_lk;
      W.release #(ht_perm sht_sig sht) sht_lk;
      W.release #(ht_perm cht_sig cht) cht_lk;
      0
    }}}
    None -> { 
    // ERROR - bad context handle
    fold (ht_perm sht_sig sht);
    fold (ht_perm cht_sig cht);
    W.release #(ht_perm sht_sig sht) sht_lk;
    W.release #(ht_perm cht_sig cht) cht_lk;
    0
    }}}
  None -> { 
  // ERROR - bad session ID
  fold (ht_perm sht_sig sht);
  W.release #(ht_perm sht_sig sht) sht_lk;
  0
  }}
}
```