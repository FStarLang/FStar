module EngineTypes
open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module US = FStar.SizeT
module U8 = FStar.UInt8
open HACL
open L0Types
open Array

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

let l0_perm (l0:l0_image_t) (vl0: l0_repr) 
  : vprop = 
  A.pts_to l0.l0_image_header full_perm vl0.l0_image_header `star`
  A.pts_to l0.l0_image_header_sig full_perm vl0.l0_image_header_sig `star`
  A.pts_to l0.l0_binary full_perm vl0.l0_binary `star`
  A.pts_to l0.l0_binary_hash full_perm vl0.l0_binary_hash `star`
  A.pts_to l0.l0_image_auth_pubkey full_perm vl0.l0_image_auth_pubkey