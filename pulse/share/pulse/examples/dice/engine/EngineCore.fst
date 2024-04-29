(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module EngineCore
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
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
fn authenticate_l0_image ([@@@ Rust_mut_binder] record:engine_record_t) (#repr:Ghost.erased engine_record_repr) (#p:perm)
    requires engine_record_perm record p repr
    returns b:(engine_record_t & bool)
    ensures (
        engine_record_perm (fst b) p repr **
        pure (snd b ==> l0_is_authentic repr)
    )
{
  unfold (engine_record_perm record p repr);

  V.to_array_pts_to record.l0_image_auth_pubkey;
  V.to_array_pts_to record.l0_image_header;
  V.to_array_pts_to record.l0_image_header_sig;  
  let valid_header_sig = ed25519_verify
                          (V.vec_to_array record.l0_image_auth_pubkey)
                          (V.vec_to_array record.l0_image_header)
                          record.l0_image_header_size
                          (V.vec_to_array record.l0_image_header_sig);
  V.to_vec_pts_to record.l0_image_auth_pubkey;
  V.to_vec_pts_to record.l0_image_header;
  V.to_vec_pts_to record.l0_image_header_sig;
  
  let mut b = false;
  if valid_header_sig
  {
    let mut hash_buf = [| 0uy; dice_digest_len |];

    V.to_array_pts_to record.l0_binary;
    hacl_hash dice_hash_alg record.l0_binary_size (V.vec_to_array record.l0_binary) hash_buf;
    V.to_vec_pts_to record.l0_binary;

    V.to_array_pts_to record.l0_binary_hash;
    let res = compare dice_digest_len hash_buf (V.vec_to_array record.l0_binary_hash);
    V.to_vec_pts_to record.l0_binary_hash;

    fold (engine_record_perm record p repr);
    let res = (record, res);
    rewrite (engine_record_perm record p repr) as
            (engine_record_perm (fst res) p repr);
    res
  }
  else
  {
    fold (engine_record_perm record p repr);
    let res = (record, false);
    rewrite (engine_record_perm record p repr) as
            (engine_record_perm (fst res) p repr);
    res
  };
}
```

```pulse
fn compute_cdi
  (cdi:A.larray U8.t (SZ.v (digest_len dice_hash_alg)))
  (uds:A.larray U8.t (US.v uds_len))
  ([@@@ Rust_mut_binder] record:engine_record_t)
  (#uds_perm #p:perm)
  (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires A.pts_to uds #uds_perm uds_bytes
        ** A.pts_to cdi 'c0
        ** engine_record_perm record p 'repr
  returns record:engine_record_t
  ensures engine_record_perm record p 'repr
       ** A.pts_to uds #uds_perm uds_bytes
       ** (exists* (c1:Seq.seq U8.t). 
            A.pts_to cdi c1 **
            pure (cdi_functional_correctness c1 uds_bytes 'repr))
{
  A.pts_to_len uds;
  let mut uds_digest = [| 0uy; dice_digest_len |];
  let mut l0_digest = [| 0uy; dice_digest_len |];
  hacl_hash dice_hash_alg uds_len uds uds_digest;

  unfold engine_record_perm record p 'repr;

  V.to_array_pts_to record.l0_binary;
  hacl_hash dice_hash_alg record.l0_binary_size (V.vec_to_array record.l0_binary) l0_digest;
  V.to_vec_pts_to record.l0_binary;

  fold engine_record_perm record p 'repr;

  hacl_hmac dice_hash_alg cdi 
    uds_digest dice_digest_len
    l0_digest dice_digest_len;
  
  record
}
```

```pulse
fn engine_main
  (cdi:A.larray U8.t (SZ.v (digest_len dice_hash_alg)))
  (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t)
  (#c0:Ghost.erased (Seq.seq U8.t))
  (#repr:Ghost.erased engine_record_repr)
  (#uds_perm #p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires engine_record_perm record p repr **
           A.pts_to uds #uds_perm uds_bytes **
           A.pts_to cdi c0
  returns  r:(engine_record_t & dice_return_code)
  ensures  engine_record_perm (fst r) p repr **
           A.pts_to uds #uds_perm uds_bytes **
          (exists* (c1:Seq.seq U8.t).
             A.pts_to cdi c1 **
             pure (snd r = DICE_SUCCESS ==> l0_is_authentic repr /\ cdi_functional_correctness c1 uds_bytes repr))
{
  let b = authenticate_l0_image record;
  if snd b 
  {
    let record = compute_cdi cdi uds (fst b);
    let res = (record, DICE_SUCCESS);
    rewrite (engine_record_perm record p repr) as
            (engine_record_perm (fst res) p repr);
    res
  }
  else
  {
    let res = (fst b, DICE_ERROR);
    rewrite (engine_record_perm (fst b) p repr) as
            (engine_record_perm (fst res) p repr);
    res    
  }
}
```
