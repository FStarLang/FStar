module DICEEngineCore
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
val spec_hash (a:alg_t) (s:Seq.seq U8.t) : Seq.lseq U8.t (US.v (digest_len a))

assume
val is_hashable_len (_:US.t) : prop

let hashable_len = v:US.t{ is_hashable_len v }

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


// DICE constants
assume
val uds_is_enabled : vprop

assume
val uds_len : hashable_len 

assume
val dice_hash_alg : alg_t


type dice_return_code = | DICE_SUCCESS | DICE_ERROR

let cdi_t = A.larray U8.t (US.v (digest_len dice_hash_alg))

noeq
type l0_image_t = {
//   l0_image_header_size : signable_len;
//   l0_image_header      : A.larray U8.t (v l0_image_header_size);
//   l0_image_header_sig  : mbuffer byte_sec 64;
   l0_binary_size : hashable_len;
   l0_binary      : A.larray U8.t (US.v l0_binary_size);
//   l0_binary_hash       : mbuffer byte_sec (v digest_len);
//   l0_image_auth_pubkey : b:mbuffer byte_sec 32
}

//[@@erasable] Could we make l0_repr erasable from the get go?
type l0_repr = {
    l0_binary      : Seq.seq U8.t;
}

// Maybe a version that doesn't give us full permission to l0?
let l0_perm (l0:l0_image_t) (vl0: l0_repr) : vprop = 
    A.pts_to l0.l0_binary full_perm vl0.l0_binary

assume
val stack_is_erased : vprop

assume
val l0_is_authentic (vl0:l0_repr) : prop

assume
val cdi_functional_correctness (cdi:Seq.seq U8.t) (vl0:l0_repr) : prop
// Roughly, we want to specify this predicate as
// cdi == spec_hmac (spec_hash dice_hash_alg uds_bytes) (spec_hash ... l0_binary)

assume
val uds_bytes : Ghost.erased (Seq.seq U8.t)

```pulse
fn authenticate_l0_image (l0:l0_image_t) (#vl0:Ghost.erased l0_repr)
    requires l0_perm l0 vl0
    returns b:bool
    ensures (
        l0_perm l0 vl0 `star`
        pure (b ==> l0_is_authentic vl0)
    )
{
    false //dummy; to be filled in with call to ED25519 etc
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


// assume
// val compute_cdi (c:cdi_t) (l0:l0_image_t) (#vl0:Ghost.erased l0_repr)
//   : stt unit  
//      (exists_ (fun (c0:Seq.seq U8.t) ->
//     uds_is_enabled `star`
//     A.pts_to c full_perm c0 `star`
//     l0_perm l0 vl0 (* should CDI only be computed on authentic l0 images? *)
//     ))
//     (fun _ ->   
//           exists_ (fun (c1:Seq.seq U8.t) ->
//             A.pts_to c full_perm c1 `star`
//             l0_perm l0 vl0 `star`
//             pure (cdi_functional_correctness c1 vl0)
//           ))




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
 ensures exists (c1:Seq.seq U8.t). (
    A.pts_to c full_perm c1 `star`
    l0_perm l0 vl0 `star`
    pure (cdi_functional_correctness c1 vl0)
 )
{
    let uds = new_array 0uy uds_len;
    let uds_digest = new_array 0uy (digest_len dice_hash_alg);
    let l0_digest = new_array 0uy (digest_len dice_hash_alg);
    read_uds uds;
    hacl_hash dice_hash_alg uds uds_len uds_digest;
    //Mysterious error above when trying to instantiate an implicit argument
    //It would be nice if it could say what it tried to match and why it didn't actually match
    //the problem was that an implicit argument of reveal was in one case an seq and another an lseq
    rewrite (l0_perm l0 vl0)
         as (A.pts_to l0.l0_binary full_perm vl0.l0_binary);
    hacl_hash dice_hash_alg l0.l0_binary l0.l0_binary_size l0_digest;
    rewrite (A.pts_to l0.l0_binary full_perm vl0.l0_binary)
         as (l0_perm l0 vl0);
    // dice_hmac alg
    //   (* dst *) st.cdi
    //   (* key *) uds_digest digest_len
    //   (* msg *) l0_digest digest_len;

    // zeroize uds_len uds;

    free_array l0_digest;
    free_array uds_digest;
    free_array uds;
    disable_uds();
    let x = ((assume false) <: (squash false));
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
    // admit() // can we have syntax for admit?
    disable_uds();
    // NB: let _ = ... does not work; you need to name the variable
    ( (assume false)  <: (squash (false)));
    ()
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