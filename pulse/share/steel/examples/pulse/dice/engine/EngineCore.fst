module EngineCore
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
open EngineTypes
open HACL

assume
val stack_is_erased : vprop

let l0_is_authentic (repr:engine_record_repr) 
  : prop
  = spec_ed25519_verify 
      repr.l0_image_auth_pubkey 
      repr.l0_image_header 
      repr.l0_image_header_sig /\
    spec_hash dice_hash_alg repr.l0_binary == repr.l0_binary_hash

let cdi_functional_correctness (c0:Seq.seq U8.t) (repr:engine_record_repr)
  : prop 
  = c0 == spec_hmac dice_hash_alg (spec_hash dice_hash_alg uds_bytes) (spec_hash dice_hash_alg repr.l0_binary)

```pulse
fn authenticate_l0_image (record:engine_record_t) (#repr:Ghost.erased engine_record_repr) (#p:perm)
    requires engine_record_perm record repr p
    returns b:bool
    ensures (
        engine_record_perm record repr p **
        pure (b ==> l0_is_authentic repr)
    )
{
  unfold engine_record_perm record repr p;

  let valid_header_sig = ed25519_verify
                          record.l0_image_auth_pubkey
                          record.l0_image_header record.l0_image_header_size
                          record.l0_image_header_sig;
  
  let mut b = false;
  if valid_header_sig {
    let hash_buf = A.alloc 0uy dice_digest_len;
    hacl_hash dice_hash_alg record.l0_binary_size record.l0_binary hash_buf;
    let res = compare dice_digest_len hash_buf record.l0_binary_hash;
    with s. assert (A.pts_to hash_buf s);
    A.free hash_buf #(coerce dice_digest_len s);
    fold engine_record_perm record repr p;
    res
  } else {
    fold engine_record_perm record repr p;
    false
  };
}
```

```pulse
fn compute_cdi (cdi:cdi_t) (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t) 
               (#repr:Ghost.erased engine_record_repr)
               (#c0:Ghost.erased (Seq.seq U8.t))
               (#uds_perm #p:perm)
  requires (
    A.pts_to uds #uds_perm uds_bytes **
    A.pts_to cdi c0 **
    engine_record_perm record repr p (* should CDI only be computed on authentic l0 images? *)
  )
  ensures (
    engine_record_perm record repr p **
    A.pts_to uds #uds_perm uds_bytes **
    exists (c1:Seq.seq U8.t). (
      A.pts_to cdi c1 **
      pure (cdi_functional_correctness c1 repr))
  )
{
    let uds_digest = A.alloc 0uy dice_digest_len;
    let l0_digest = A.alloc 0uy dice_digest_len;
    hacl_hash dice_hash_alg uds_len uds uds_digest #uds_perm #(coerce uds_len uds_bytes);

    unfold engine_record_perm record repr p;
    hacl_hash dice_hash_alg record.l0_binary_size record.l0_binary l0_digest;
    fold engine_record_perm record repr p;

    dice_digest_len_is_hashable;

    hacl_hmac dice_hash_alg cdi 
      uds_digest dice_digest_len
      l0_digest dice_digest_len;

    A.free l0_digest;
    A.free uds_digest;
    ()
}
```

#set-options "--print_implicits --print_universes"
```pulse
fn engine_main' (cdi:cdi_t) (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t)
                (#c0:Ghost.erased (elseq U8.t dice_digest_len))
                (#repr:Ghost.erased engine_record_repr)
                (#uds_perm #p:perm)
  requires (
    engine_record_perm record repr p **
    A.pts_to uds #uds_perm uds_bytes **
    A.pts_to cdi c0
  )
  returns r:dice_return_code
  ensures (
    engine_record_perm record repr p **
    A.pts_to uds #uds_perm uds_bytes **
    exists (c1:elseq U8.t dice_digest_len). (
      A.pts_to cdi c1 **
      pure (
        A.is_full_array cdi /\
        r = DICE_SUCCESS ==> l0_is_authentic repr /\ cdi_functional_correctness c1 repr
      )
  ))
{
  let b = authenticate_l0_image record;
  if b 
  {
    compute_cdi cdi uds record #repr #(coerce dice_digest_len c0);
    with s. assert (A.pts_to uds #uds_perm s);
    DICE_SUCCESS
  } else { DICE_ERROR }
}
```
let engine_main = engine_main'