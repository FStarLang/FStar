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

module HACL
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

let v32us : US.t = 32sz

// let coerce (l:US.t) (s:erased (elseq U8.t l)) : erased (Seq.seq U8.t)
//   = let s_ = reveal s in 
//     hide s_

// let coerce_refined (l:US.t) (s:erased (Seq.seq U8.t){Seq.length (reveal s) == US.v l}) : erased (elseq U8.t l)
//   = let s_ = reveal s in 
//     hide s_

(* a tiny model of HACL* hashes *)

val alg_t : Type0

val digest_len (_:alg_t) : US.t

val is_hashable_len (_:US.t) : prop

let hashable_len = v:US.t{ is_hashable_len v }

val is_signable_len (_:US.t) : prop

let signable_len = v:US.t{ is_signable_len v }

val valid_hkdf_lbl_len (l:US.t) : prop

let hkdf_lbl_len = v:US.t{ valid_hkdf_lbl_len v }

val valid_hkdf_ikm_len (_:US.t) : prop

let hkdf_ikm_len = v:US.t{ valid_hkdf_ikm_len v }

noextract [@@noextract_to "krml"]
val spec_hash 
  (a:alg_t) 
  (s:Seq.seq U8.t) 
  : s:(Seq.seq U8.t){ Seq.length s = (US.v (digest_len a)) }

val hacl_hash (alg:alg_t)
              (src_len: hashable_len)
              (src:A.larray U8.t (US.v src_len))
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (#psrc:perm)
              (#src_seq #dst_seq:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to dst dst_seq **
     A.pts_to src #psrc src_seq)
    (fun _ ->
       A.pts_to src #psrc src_seq **
       A.pts_to dst (spec_hash alg src_seq))

noextract [@@noextract_to "krml"]
val spec_hmac 
  (a:alg_t) 
  (k:Seq.seq U8.t) 
  (m:Seq.seq U8.t) 
  : s:(Seq.seq U8.t){ Seq.length s = (US.v (digest_len a)) }

val hacl_hmac (alg:alg_t)
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (key:A.array U8.t)
              (key_len: hashable_len { US.v key_len == A.length key })
              (msg:A.array U8.t)
              (msg_len: hashable_len { US.v msg_len == A.length msg })
              (#pkey #pmsg:perm)
              (#dst_seq:erased (Seq.seq U8.t))
              (#key_seq:erased (Seq.seq U8.t))
              (#msg_seq:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to dst dst_seq **
     A.pts_to key #pkey key_seq **
     A.pts_to msg #pmsg msg_seq)
    (fun _ ->
       A.pts_to key #pkey key_seq **
       A.pts_to msg #pmsg msg_seq **
       A.pts_to dst (spec_hmac alg key_seq msg_seq))

val spec_ed25519_verify (pubk hdr sig:Seq.seq U8.t) : prop 

val ed25519_verify 
  (pubk:A.larray U8.t (US.v v32us))
  (hdr:A.array U8.t)
  (hdr_len:signable_len { US.v hdr_len == A.length hdr })
  (sig:A.larray U8.t 64)
  (#ppubk #phdr #psig:perm)
  (#pubk_seq #hdr_seq #sig_seq:erased (Seq.seq U8.t))
  : stt bool
    (A.pts_to pubk #ppubk pubk_seq **
     A.pts_to hdr #phdr hdr_seq **
     A.pts_to sig #psig sig_seq)
    (fun res ->
      A.pts_to pubk #ppubk pubk_seq **
      A.pts_to hdr #phdr hdr_seq **
      A.pts_to sig #psig sig_seq **
      pure (res == true <==> spec_ed25519_verify pubk_seq hdr_seq sig_seq))

noextract [@@noextract_to "krml"]
val spec_ed25519_sign (privk msg:Seq.seq U8.t) : Seq.seq U8.t

val ed25519_sign 
  (buf:A.larray U8.t 64)
  (privk:A.larray U8.t (US.v v32us))
  (len:US.t { US.v len < pow2 32 })
  (msg:A.larray U8.t (US.v len))
  (#pprivk #pmsg:perm)
  (#buf0 #privk_seq #msg_seq:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to buf buf0 **
     A.pts_to privk #pprivk privk_seq **
     A.pts_to msg #pmsg msg_seq)
    (fun _ -> exists* (buf1:Seq.seq U8.t).
      A.pts_to buf buf1 ** 
      A.pts_to privk #pprivk privk_seq **
      A.pts_to msg #pmsg msg_seq **
      pure (buf1 `Seq.equal` spec_ed25519_sign privk_seq msg_seq))

(* DICE hash constants *)

// NOTE: I added a unit argument to avoid krmlinit_globals

val dice_hash_alg0 (_: unit) : alg_t

inline_for_extraction noextract [@@noextract_to "krml"]
let dice_hash_alg = dice_hash_alg0 ()

inline_for_extraction noextract [@@noextract_to "krml"]
let dice_digest_len : hashable_len = assume (is_hashable_len (digest_len dice_hash_alg)); digest_len dice_hash_alg

assume Dice_digest_len_is_hashable : is_hashable_len dice_digest_len

assume Dice_digest_len_is_hkdf_ikm : valid_hkdf_ikm_len dice_digest_len

assume Is_hashable_len_32 : is_hashable_len v32us
