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

let cdi_functional_correctness (c0:Seq.seq U8.t) (uds_bytes:Seq.seq U8.t) (repr:engine_record_repr)
  : prop 
  = Seq.length uds_bytes == US.v uds_len /\
    c0 == spec_hmac dice_hash_alg (spec_hash dice_hash_alg uds_bytes) (spec_hash dice_hash_alg repr.l0_binary)

```pulse
fn authenticate_l0_image (record:engine_record_t) (#repr:Ghost.erased engine_record_repr) (#p:perm)
    requires engine_record_perm record p repr
    returns b:bool
    ensures (
        engine_record_perm record p repr **
        pure (b ==> l0_is_authentic repr)
    )
{
  unfold (engine_record_perm record p repr);

  let valid_header_sig = ed25519_verify
                          record.l0_image_auth_pubkey
                          record.l0_image_header record.l0_image_header_size
                          record.l0_image_header_sig;
  
  let mut b = false;
  if valid_header_sig
  {
    let hash_buf = A.alloc 0uy dice_digest_len;
    hacl_hash dice_hash_alg record.l0_binary_size record.l0_binary hash_buf;
    let res = compare dice_digest_len hash_buf record.l0_binary_hash;
    A.free hash_buf;
    fold (engine_record_perm record p repr);
    res
  }
  else
  {
    fold (engine_record_perm record p repr);
    false
  };
}
```

```pulse
fn compute_cdi (cdi:cdi_t) (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t) 
               (#uds_perm #p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires A.pts_to uds #uds_perm uds_bytes
        ** A.pts_to cdi 'c0
        ** engine_record_perm record p 'repr
  ensures engine_record_perm record p 'repr
       ** A.pts_to uds #uds_perm uds_bytes
       ** exists (c1:Seq.seq U8.t). 
            A.pts_to cdi c1 **
            pure (cdi_functional_correctness c1 uds_bytes 'repr)
{
  A.pts_to_len uds;
  let uds_digest = A.alloc 0uy dice_digest_len;
  let l0_digest = A.alloc 0uy dice_digest_len;
  hacl_hash dice_hash_alg uds_len uds uds_digest;

  unfold engine_record_perm record p 'repr;
  hacl_hash dice_hash_alg record.l0_binary_size record.l0_binary l0_digest;
  fold engine_record_perm record p 'repr;

  dice_digest_len_is_hashable;

  hacl_hmac dice_hash_alg cdi 
    uds_digest dice_digest_len
    l0_digest dice_digest_len;

  A.free l0_digest;
  A.free uds_digest;
}
```

```pulse
fn engine_main' (cdi:cdi_t) (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t)
                (#c0:Ghost.erased (Seq.seq U8.t))
                (#repr:Ghost.erased engine_record_repr)
                (#uds_perm #p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires engine_record_perm record p repr **
           A.pts_to uds #uds_perm uds_bytes **
           A.pts_to cdi c0
  returns  r:dice_return_code
  ensures  engine_record_perm record p repr **
           A.pts_to uds #uds_perm uds_bytes **
           exists (c1:Seq.seq U8.t).
             A.pts_to cdi c1 **
             pure (r = DICE_SUCCESS ==> l0_is_authentic repr /\ cdi_functional_correctness c1 uds_bytes repr)
{
  let b = authenticate_l0_image record;
  if b 
  {
    compute_cdi cdi uds record;
    DICE_SUCCESS
  }
  else
  { 
    DICE_ERROR
  }
}
```
let engine_main = engine_main'