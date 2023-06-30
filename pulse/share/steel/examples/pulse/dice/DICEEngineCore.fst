module DICEEngineCore
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
open HACL
open L0Types
open Array

// DICE constants

assume
val uds_is_enabled : vprop

assume
val uds_len : hashable_len 

type dice_return_code = | DICE_SUCCESS | DICE_ERROR

let cdi_t = A.larray U8.t (US.v (digest_len dice_hash_alg))

noeq
type l0_image_t = {
  l0_image_header_size : signable_len;
  l0_image_header      : A.larray U8.t (US.v l0_image_header_size);
  l0_image_header_sig  : A.larray U8.t 64; (* secret bytes *)
  l0_binary_size       : hashable_len;
  l0_binary            : A.larray U8.t (US.v l0_binary_size);
  l0_binary_hash       : A.larray U8.t (US.v dice_digest_len); (*secret bytes *)
  l0_image_auth_pubkey : A.larray U8.t 32; (* secret bytes *)
}

//[@@erasable] Could we make l0_repr erasable from the get go?
type l0_repr = {
    l0_image_header      : Seq.seq U8.t;
    l0_image_header_sig  : Seq.seq U8.t;
    l0_binary            : Seq.seq U8.t;
    l0_binary_hash       : (s:Seq.seq U8.t{ Seq.length s = US.v dice_digest_len });
    l0_image_auth_pubkey : Seq.seq U8.t;
}

let l0_perm (l0:l0_image_t) (vl0: l0_repr) : vprop = 
  A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
  A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
  A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
  A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
  A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey

assume
val uds_bytes : v:(Ghost.erased (Seq.seq U8.t)){ Seq.length v = US.v uds_len }

assume
val stack_is_erased : vprop

let l0_is_authentic (vl0:l0_repr) 
  : prop
  = spec_ed25519_verify 
      vl0.l0_image_auth_pubkey 
      vl0.l0_image_header 
      vl0.l0_image_header_sig /\
    spec_hash dice_hash_alg vl0.l0_binary == vl0.l0_binary_hash

let cdi_functional_correctness (c0:Seq.seq U8.t) (vl0:l0_repr)
  : prop 
  = c0 == spec_hmac dice_hash_alg (spec_hash dice_hash_alg uds_bytes) (spec_hash dice_hash_alg vl0.l0_binary)

// DICE engine functionality 

```pulse
fn authenticate_l0_image (l0:l0_image_t) (#vl0:Ghost.erased l0_repr)
    requires l0_perm l0 vl0
    returns b:bool
    ensures (
        l0_perm l0 vl0 `star`
        pure (b ==> l0_is_authentic vl0)
    )
{
  unfold l0_perm l0 vl0;

  let valid_header_sig = ed25519_verify
                          l0.l0_image_auth_pubkey
                          l0.l0_image_header l0.l0_image_header_size
                          l0.l0_image_header_sig;
  
  let mut b = false;
  if valid_header_sig {
    let hash_buf = new_array 0uy dice_digest_len;
    hacl_hash dice_hash_alg l0.l0_binary l0.l0_binary_size hash_buf;
    let res = compare dice_digest_len hash_buf l0.l0_binary_hash;
    free_array hash_buf;
    fold l0_perm l0 vl0;
    res
  } else {
    fold l0_perm l0 vl0;
    false
  };
}
```

assume
val drop (p:vprop)
    : stt unit p (fun _ -> emp)

```pulse
fn disable_uds (_:unit) 
    requires uds_is_enabled
    ensures emp
{
    drop uds_is_enabled
}
```

```pulse
fn zeroize_uds (uds:A.array U8.t) 
               (l:(l:US.t{ US.v l = A.length uds })) 
               (#uds0:(uds0:Ghost.erased (Seq.seq U8.t) { Seq.length uds0 = A.length uds }))
  requires (
    uds_is_enabled `star`
    A.pts_to uds full_perm uds0
  )
  ensures (
    uds_is_enabled `star`
    (exists_ (fun (uds1:Seq.seq U8.t) ->   
      A.pts_to uds full_perm uds1 `star`
      pure (uds1 `Seq.equal` Seq.create (US.v l) 0uy)))
  )
{
  fill_array l uds 0uy;
}
```

assume
val read_uds (uds:A.larray U8.t (US.v uds_len))
             (#s:Ghost.erased (Seq.seq U8.t))
  : stt unit 
      (A.pts_to uds full_perm s `star` uds_is_enabled)
      (fun _ -> A.pts_to uds full_perm uds_bytes `star` uds_is_enabled)

(* Pulse desugaring seems to allow the val to be in scope, even though it is not assumed *)
val free_array_u8 (a: A.array U8.t)
  : stt unit
    (exists_ (fun (x:Seq.seq U8.t) -> A.pts_to a full_perm x) `star` pure (A.is_full_array a))
    (fun _ -> emp)

```pulse
fn compute_cdi (c:cdi_t) (l0:l0_image_t) 
               (#vl0:Ghost.erased l0_repr)
               (#c0:Ghost.erased (Seq.seq U8.t))
  requires (
    uds_is_enabled `star`
    A.pts_to c full_perm c0 `star`
    l0_perm l0 vl0 (* should CDI only be computed on authentic l0 images? *)
  )
  ensures (
    l0_perm l0 vl0 `star`
    (exists_ (fun (c1:Seq.seq U8.t) ->
      A.pts_to c full_perm c1 `star`
      pure (cdi_functional_correctness c1 vl0)))
  )
{
    let uds = new_array 0uy uds_len;
    let uds_digest = new_array 0uy dice_digest_len;
    let l0_digest = new_array 0uy dice_digest_len;
    read_uds uds;
    hacl_hash dice_hash_alg uds uds_len uds_digest;

    unfold l0_perm l0 vl0;
    hacl_hash dice_hash_alg l0.l0_binary l0.l0_binary_size l0_digest;
    fold l0_perm l0 vl0;

    dice_digest_len_is_hashable;

    hacl_hmac dice_hash_alg c 
      uds_digest dice_digest_len
      l0_digest dice_digest_len;

    zeroize_uds uds uds_len;

    free_array l0_digest;
    free_array uds_digest;
    free_array uds;
    disable_uds();
    ()
}
```

```pulse
fn dice_main (c:cdi_t) (l0:l0_image_t)
             (#vl0:Ghost.erased l0_repr)
             (#c0:Ghost.erased (Seq.seq U8.t))
  requires (
    uds_is_enabled `star`
    A.pts_to c full_perm c0 `star`
    l0_perm l0 vl0
  )
  returns r: dice_return_code
  ensures exists (c1:Seq.seq U8.t). (
      A.pts_to c full_perm c1 `star`
      l0_perm l0 vl0 `star`
      pure (r == DICE_SUCCESS ==> l0_is_authentic vl0 /\ cdi_functional_correctness c1 vl0)
  )
{
  let b = authenticate_l0_image l0;
  if b 
  {
    compute_cdi c l0;
    DICE_SUCCESS
  }
  else
  {
    disable_uds ();
    DICE_ERROR
  }
}
```
