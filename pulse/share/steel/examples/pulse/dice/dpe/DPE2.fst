module DPE2
open Pulse.Lib.Pervasives
open HACL
open X509
open EngineTypes
open EngineCore
open L0Types
open L0Core
module L = Pulse.Lib.SpinLock
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open LinearScanHashTable
open PulseHashTable
module PHT = PulseHashTable
module LSHT = LinearScanHashTable
open Pulse.Class.BoundedIntegers
open DPE

(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table. Return the new context handle upon
  success and 0 upon failure. 
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
  L.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with spht. assert (models sht_sig sht spht);

  let res = PHT.lookup #sht_sig #spht sht sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht = dfst locked_cht;
      let cht_lk = dsnd locked_cht;
      L.acquire #(ht_perm cht_sig cht) cht_lk;

      unfold (ht_perm cht_sig cht);
      with cpht. assert (models cht_sig cht cpht);

      let r = PHT.lookup #cht_sig #cpht cht ctxt_hndl;
      if (fst r) {
        let opt_locked_ctxt = snd r;
        match opt_locked_ctxt {
        Some locked_ctxt -> {
        let ctxt = dfst locked_ctxt;
        let ctxt_lk = dsnd locked_ctxt;
        L.acquire #(context_perm ctxt) ctxt_lk;

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

              let cdi = A.alloc 0uy dice_digest_len;
              let ret = EngineCore.engine_main cdi c.uds r;
              with s. assert (A.pts_to cdi full_perm s);
              A.free c.uds;

              match ret {
              DICE_SUCCESS -> {
                let new_locked_context = init_l0_ctxt cdi;
                A.free cdi #(coerce dice_digest_len s);
                
                let d = PHT.delete #cht_sig #cpht cht ctxt_hndl;
                if d {
                  assert (models cht_sig cht (LSHT.delete cpht ctxt_hndl));
                  let b = not_full #cht_sig #(LSHT.delete cpht ctxt_hndl) cht;
                  if b {
                    let i = PHT.insert #cht_sig #(LSHT.delete cpht ctxt_hndl) cht new_ctxt_hndl new_locked_context; 
                    if i {
                      assert (models cht_sig cht (LSHT.insert (LSHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                      rewrite (engine_record_perm r r0) as (record_perm record repr);
                      fold (ht_perm sht_sig sht);
                      fold (ht_perm cht_sig cht);
                      L.release #(ht_perm sht_sig sht) sht_lk;
                      L.release #(ht_perm cht_sig cht) cht_lk;
                      new_ctxt_hndl
                    } else {
                      // ERROR - insert failed
                      assert (models cht_sig cht (LSHT.delete cpht ctxt_hndl));
                      rewrite (engine_record_perm r r0) as (record_perm record repr);
                      fold (ht_perm sht_sig sht);
                      fold (ht_perm cht_sig cht);
                      L.release #(ht_perm sht_sig sht) sht_lk;
                      L.release #(ht_perm cht_sig cht) cht_lk;
                      0
                  }} else {
                    // ERROR -- table full
                    rewrite (engine_record_perm r r0) as (record_perm record repr);
                    fold (ht_perm sht_sig sht);
                    fold (ht_perm cht_sig cht);
                    L.release #(ht_perm sht_sig sht) sht_lk;
                    L.release #(ht_perm cht_sig cht) cht_lk;
                    0
                }} else {
                  // ERROR - delete failed
                  assert (models cht_sig cht cpht);
                  rewrite (engine_record_perm r r0) as (record_perm record repr);
                  fold (ht_perm sht_sig sht);
                  fold (ht_perm cht_sig cht);
                  L.release #(ht_perm sht_sig sht) sht_lk;
                  L.release #(ht_perm cht_sig cht) cht_lk;
                  0
                }}
              DICE_ERROR -> {
                // ERROR -- DICE engine failed
                A.free cdi #(coerce dice_digest_len s);
                rewrite (engine_record_perm r r0) as (record_perm record repr);
                fold (ht_perm sht_sig sht);
                fold (ht_perm cht_sig cht);
                L.release #(ht_perm sht_sig sht) sht_lk;
                L.release #(ht_perm cht_sig cht) cht_lk;
                0
              }}}
            _ -> {
              // ERROR - repr should have type (Egnine_repr r0)
              zeroize uds_len c.uds #uds_bytes;
              disable_uds ();
              A.free c.uds;

              fold (ht_perm sht_sig sht);
              fold (ht_perm cht_sig cht);
              L.release #(ht_perm sht_sig sht) sht_lk;
              L.release #(ht_perm cht_sig cht) cht_lk;
              0
            }}
          }
          _ -> {
            // ERROR - record should have type (Engine_record r)
            zeroize uds_len c.uds;
            disable_uds ();
            A.free c.uds;

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            L.release #(ht_perm sht_sig sht) sht_lk;
            L.release #(ht_perm cht_sig cht) cht_lk;
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

              let deviceID_pub = A.alloc 0uy v32us;
              let deviceID_priv = A.alloc 0uy v32us;
              let aliasKey_pub = A.alloc 0uy v32us;
              let aliasKey_priv = A.alloc 0uy v32us;
              let deviceIDCSR = A.alloc 0uy deviceIDCSR_len;
              let aliasKeyCRT = A.alloc 0uy aliasKeyCRT_len;

              rewrite (record_perm record repr) as (l0_record_perm r r0); 

              assume_ (pure(valid_hkdf_ikm_len (digest_len dice_hash_alg)));
              
              L0Core.l0_main  c.cdi deviceID_pub deviceID_priv 
                              aliasKey_pub aliasKey_priv 
                              aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT 
                              deviceIDCRI_len deviceIDCSR_len deviceIDCSR r;
              A.free c.cdi;

              with (s1:elseq U8.t v32us). assert (A.pts_to aliasKey_priv full_perm s1);
              let new_locked_context = init_l1_ctxt deviceIDCSR_len aliasKeyCRT_len 
                                                    deviceID_priv deviceID_pub
                                                    aliasKey_priv aliasKey_pub 
                                                    deviceIDCSR aliasKeyCRT;
              A.free deviceID_pub;
              A.free deviceID_priv;
              A.free aliasKey_pub;
              A.free aliasKey_priv;
              A.free deviceIDCSR;
              A.free aliasKeyCRT;
              
              let d = PHT.delete #cht_sig #cpht cht ctxt_hndl;
              if d {
                assert (models cht_sig cht (LSHT.delete cpht ctxt_hndl));
                let b = not_full #cht_sig #(LSHT.delete cpht ctxt_hndl) cht;
                if b {
                  let i = PHT.insert #cht_sig #(LSHT.delete cpht ctxt_hndl) cht new_ctxt_hndl new_locked_context;
                  if i {
                    assert (models cht_sig cht (LSHT.insert (LSHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                    rewrite (l0_record_perm r r0) as (record_perm record repr);
                    fold (ht_perm sht_sig sht);
                    fold (ht_perm cht_sig cht);
                    L.release #(ht_perm sht_sig sht) sht_lk;
                    L.release #(ht_perm cht_sig cht) cht_lk;
                    new_ctxt_hndl
                  } else {
                    // ERROR - insert failed
                    assert (models cht_sig cht (LSHT.delete cpht ctxt_hndl));
                    rewrite (l0_record_perm r r0) as (record_perm record repr);
                    fold (ht_perm sht_sig sht);
                    fold (ht_perm cht_sig cht);
                    L.release #(ht_perm sht_sig sht) sht_lk;
                    L.release #(ht_perm cht_sig cht) cht_lk;
                    0
                }} else {
                  // ERROR - table full
                  rewrite (l0_record_perm r r0) as (record_perm record repr);
                  fold (ht_perm sht_sig sht);
                  fold (ht_perm cht_sig cht);
                  L.release #(ht_perm sht_sig sht) sht_lk;
                  L.release #(ht_perm cht_sig cht) cht_lk;
                  0
              }} else {
                // ERROR - delete failed
                assert (models cht_sig cht cpht);
                rewrite (l0_record_perm r r0) as (record_perm record repr);
                fold (ht_perm sht_sig sht);
                fold (ht_perm cht_sig cht);
                L.release #(ht_perm sht_sig sht) sht_lk;
                L.release #(ht_perm cht_sig cht) cht_lk;
                0
              }
            }
            _ -> {
              // ERROR - repr should have type (L0_repr r0)
              zeroize dice_digest_len c.cdi;
              A.free c.cdi;

              fold (ht_perm sht_sig sht);
              fold (ht_perm cht_sig cht);
              L.release #(ht_perm sht_sig sht) sht_lk;
              L.release #(ht_perm cht_sig cht) cht_lk;
              0
            }}
          }
          _ -> {
            // ERROR - record should have type (L0_record r)
            zeroize dice_digest_len c.cdi;
            A.free c.cdi;

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            L.release #(ht_perm sht_sig sht) sht_lk;
            L.release #(ht_perm cht_sig cht) cht_lk;
            0
          }}
        }
        _ -> { 
          // ERROR - cannot invoke DeriveChild with L1 context
          fold (ht_perm sht_sig sht);
          fold (ht_perm cht_sig cht);
          L.release #(context_perm ctxt) ctxt_lk;
          L.release #(ht_perm sht_sig sht) sht_lk;
          L.release #(ht_perm cht_sig cht) cht_lk;
          0
        }}}
        None -> { 
        // ERROR - bad context handle
        fold (ht_perm sht_sig sht);
        fold (ht_perm cht_sig cht);
        L.release #(ht_perm sht_sig sht) sht_lk;
        L.release #(ht_perm cht_sig cht) cht_lk;
        0
        }}
      } else {
        // ERROR - lookup failed
        fold (ht_perm sht_sig sht);
        fold (ht_perm cht_sig cht);
        L.release #(ht_perm sht_sig sht) sht_lk;
        L.release #(ht_perm cht_sig cht) cht_lk;
        0
      }}
    None -> { 
    // ERROR - bad session ID
    fold (ht_perm sht_sig sht);
    L.release #(ht_perm sht_sig sht) sht_lk;
    0
    }}
  } else {
    // ERROR - lookup failed
    fold (ht_perm sht_sig sht);
    L.release #(ht_perm sht_sig sht) sht_lk;
    0
  }
}
```