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

(* a tiny model of HACL* hashes *)
assume
val alg_t : Type0

assume
val digest_len (_:alg_t) : US.t

assume
val is_hashable_len (_:US.t) : prop

let hashable_len = v:US.t{ is_hashable_len v }

assume
val is_signable_len (_:US.t) : prop

let signable_len = v:US.t{ is_signable_len v }

let key_len = v:US.t{ is_hashable_len v }

assume
val spec_hash (a:alg_t) (s:Seq.seq U8.t) : s:(Seq.seq U8.t){ Seq.length s = (US.v (digest_len a)) }

assume
val hacl_hash (alg:alg_t)
              (src:A.array U8.t) 
              (src_len: hashable_len { US.v src_len == A.length src })
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (#psrc:perm)
              (#src_seq:Ghost.erased (Seq.seq U8.t))
              (#dst_seq:Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to dst full_perm dst_seq `star`
     A.pts_to src psrc src_seq)
    (fun _ ->
       A.pts_to src psrc src_seq `star`
       A.pts_to dst full_perm (spec_hash alg src_seq))

assume
val spec_hmac (a:alg_t) (k:Seq.seq U8.t) (m:Seq.seq U8.t) : s:(Seq.seq U8.t){ Seq.length s = (US.v (digest_len a)) }

assume
val hacl_hmac (alg:alg_t)
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (key:A.array U8.t)
              (key_len: key_len { US.v key_len == A.length key })
              (msg:A.array U8.t)
              (msg_len: hashable_len { US.v msg_len == A.length msg })
              (#pkey #pmsg:perm)
              (#dst_seq:Ghost.erased (Seq.seq U8.t))
              (#key_seq:Ghost.erased (Seq.seq U8.t))
              (#msg_seq:Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to dst full_perm dst_seq `star`
     A.pts_to key pkey key_seq `star`
     A.pts_to msg pmsg msg_seq)
    (fun _ ->
       A.pts_to key pkey key_seq `star`
       A.pts_to msg pmsg msg_seq `star`
       A.pts_to dst full_perm (spec_hmac alg key_seq msg_seq))

assume
val spec_ed25519_verify (pubk hdr sig:Seq.seq U8.t) : prop 

assume
val ed25519_verify 
  (pubk:A.larray U8.t 32)
  (hdr:A.array U8.t)
  (hdr_len:signable_len { US.v hdr_len == A.length hdr })
  (sig:A.larray U8.t 64)
  (#ppubk #phdr #psig:perm)
  (#pubk_seq #hdr_seq #sig_seq:Ghost.erased (Seq.seq U8.t))
  : stt bool
    (A.pts_to pubk ppubk pubk_seq `star`
     A.pts_to hdr phdr hdr_seq `star`
     A.pts_to sig psig sig_seq)
    (fun _ ->
      A.pts_to pubk ppubk pubk_seq `star`
      A.pts_to hdr phdr hdr_seq `star`
      A.pts_to sig psig sig_seq `star`
      pure (spec_ed25519_verify pubk_seq hdr_seq sig_seq))

// DICE constants
assume
val uds_is_enabled : vprop

assume
val uds_len : hashable_len 

assume
val dice_hash_alg : alg_t

let dice_digest_len : US.t = (digest_len dice_hash_alg)

assume 
val dice_digest_len_is_hashable 
  : is_hashable_len dice_digest_len

type dice_return_code = | DICE_SUCCESS | DICE_ERROR

let cdi_t = A.larray U8.t (US.v (digest_len dice_hash_alg))

noeq
type l0_image_t = {
  l0_image_header_size : signable_len;
  l0_image_header      : A.larray U8.t (US.v l0_image_header_size);
  l0_image_header_sig  : A.larray U8.t 64; (* should be secret bytes *)
  l0_binary_size       : hashable_len;
  l0_binary            : A.larray U8.t (US.v l0_binary_size);
  l0_binary_hash       : A.larray U8.t (US.v dice_digest_len); (* should be secret bytes, digest len should be poly in alg *)
  l0_image_auth_pubkey : A.larray U8.t 32; (* should be secret bytes *)
}

//[@@erasable] Could we make l0_repr erasable from the get go?
type l0_repr = {
    l0_image_header      : Seq.seq U8.t;
    l0_image_header_sig  : Seq.seq U8.t;
    l0_binary            : Seq.seq U8.t;
    l0_binary_hash       : Seq.seq U8.t;
    l0_image_auth_pubkey : Seq.seq U8.t;
}

// Maybe a version that doesn't give us full permission to l0?
let l0_perm (l0:l0_image_t) (vl0: l0_repr) : vprop = 
  A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
  A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
  A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
  A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
  A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey

// let get_l0_binary_perm (l0:l0_image_t) (vl0: l0_repr)
//   = l0_perm l0 vl0 ==> A.pts_to l0.l0_binary full_perm vl0.l0_binary

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

```pulse
fn authenticate_l0_image (l0:l0_image_t) (#vl0:Ghost.erased l0_repr)
    requires l0_perm l0 vl0
    returns b:bool
    ensures (
        l0_perm l0 vl0 `star`
        pure (b ==> l0_is_authentic vl0)
    )
{
  rewrite (l0_perm l0 vl0)
    as (A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
      A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
      A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
      A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
      A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey);

  let valid_header_sig = ed25519_verify
                          l0.l0_image_auth_pubkey
                          l0.l0_image_header l0.l0_image_header_size
                          l0.l0_image_header_sig;
  
  let mut b = false;
  if valid_header_sig {
    let hash_buf = new_array 0uy dice_digest_len;
    hacl_hash dice_hash_alg l0.l0_binary l0.l0_binary_size hash_buf;
    // let res = A.compare hash_buf l0.l0_binary_hash dice_digest_len;
    if true {
      free_array hash_buf;
      rewrite (A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
          A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
          A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
          A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
          A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey)
        as (l0_perm l0 vl0);
      // true
      false
    } else {
      free_array hash_buf;
      rewrite (A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
          A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
          A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
          A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
          A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey)
        as (l0_perm l0 vl0);
      false
    }
  } else {
    rewrite (A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
        A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
        A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
        A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
        A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey)
      as (l0_perm l0 vl0);
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

let seq_constant_until (#t:Type) (s:Seq.seq t) (v:t) (n:nat) =
    forall (i:nat). i < n /\ i < Seq.length s ==> Seq.index s i == v

```pulse
fn fill_array (#t:Type0) (a:A.array t) (l:(l:US.t { US.v l == A.length a })) (v:t)
              (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == A.length a }))
   requires (A.pts_to a full_perm s)
   ensures 
      exists (s:Seq.seq t). (
         A.pts_to a full_perm s `star`
         pure (seq_constant_until s v (US.v l))
      )
{
   let mut i = 0sz;
   while (let vi = !i; US.(vi <^ l))
   invariant b. exists (s:Seq.seq t) (vi:US.t). ( 
      A.pts_to a full_perm s `star`
      R.pts_to i full_perm vi `star`
      pure ((b == US.(vi <^ l)) /\
            US.v vi <= US.v l /\
            Seq.length s == A.length a /\
            seq_constant_until s v (US.v vi))
   )
   {
      let vi = !i; 
      (a.(vi) <- v);
      i := US.(vi +^ 1sz);
      ()
   };
   ()
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
    (exists_ (fun (uds':Seq.seq U8.t) ->   
      A.pts_to uds full_perm uds' `star`
      pure (seq_constant_until uds' 0uy (US.v l))))
  )
{
  fill_array uds l 0uy;
}
```

assume
val read_uds (uds:A.larray U8.t (US.v uds_len))
             (#s:Ghost.erased (Seq.seq U8.t))
  : stt unit 
      (A.pts_to uds full_perm s `star` uds_is_enabled)
      (fun _ -> A.pts_to uds full_perm uds_bytes `star` uds_is_enabled)

(* Pulse desugaring seems to allow the val to be in scope, even though it is not assumed *)
(* Also the polymorphic version doesn't work *)
val free_array_u8
      (a: A.array U8.t)
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
    //Mysterious error above when trying to instantiate an implicit argument
    //It would be nice if it could say what it tried to match and why it didn't actually match
    //the problem was that an implicit argument of reveal was in one case an seq and another an lseq
    rewrite (l0_perm l0 vl0)
         as (A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
            A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
            A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
            A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
            A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey);
    hacl_hash dice_hash_alg l0.l0_binary l0.l0_binary_size l0_digest;
    rewrite (A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
            A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
            A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
            A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
            A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey)
         as (l0_perm l0 vl0);

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
    compute_cdi c l0; //Initially, we partially applied compute_cdi c; and were very confused; can we warn on partial applications?
    DICE_SUCCESS
  }
  else
  {
    disable_uds ();
    DICE_ERROR
  }
}
```

(*
```pulse
fn compute_cdi_v2 (c:cdi_t) (l0:l0_image_t) (#vl0:Ghost.erased l0_repr)
 requires exists (c0: Seq.seq U8.t). (
    uds_is_enabled `star`
    A.pts_to c full_perm c0 `star`
    l0_perm l0 vl0 (* should CDI only be computed on authentic l0 images? *)
 )
 ensures exists (c1:Seq.seq U8.t). (
    A.pts_to c full_perm c1 `star`
    l0_perm l0 vl0 `star`
    pure (cdi_functional_correctness c1 vl0)
 )
{
    disable_uds();
    admit() //NB: let _ does not work
}
```

// #push-options "--fuel 0 --ifuel 1"
```pulse
fn dice_main_v2 (c:cdi_t) (l0:l0_image_t) (#vl0:Ghost.erased l0_repr)
  requires exists (c0:Seq.seq U8.t). (
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
    //Note, compute_cdi's implicit arg vl0 appears beneath an existential
    //and the current implicit arg solver does not descend into existentials
    //so we needed to instantiate manually
    //The new solver should hande this case
    compute_cdi c l0 #vl0; 
    DICE_SUCCESS
  }
  else
  {
    disable_uds ();
    DICE_ERROR
  }
}
```
*)