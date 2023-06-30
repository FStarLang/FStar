module HACL
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

let elseq (a:Type) (l:nat) = s:Ghost.erased (Seq.seq a) { Seq.length s == l }

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

assume
val valid_hkdf_lbl_len (l:US.t) : prop

let hkdf_lbl_len = v:US.t{ valid_hkdf_lbl_len v }

assume
val valid_hkdf_ikm_len (_:US.t) : prop

let hkdf_ikm_len = v:US.t{ valid_hkdf_ikm_len v }

assume
val spec_hash 
  (a:alg_t) 
  (s:Seq.seq U8.t) 
  : s:(Seq.seq U8.t){ Seq.length s = (US.v (digest_len a)) }

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
val spec_hmac 
  (a:alg_t) 
  (k:Seq.seq U8.t) 
  (m:Seq.seq U8.t) 
  : s:(Seq.seq U8.t){ Seq.length s = (US.v (digest_len a)) }

assume
val hacl_hmac (alg:alg_t)
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (key:A.array U8.t)
              (key_len: hashable_len { US.v key_len == A.length key })
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

assume
val spec_ed25519_sign (privk msg:Seq.seq U8.t) : Seq.seq U8.t

assume
val ed25519_sign 
  (buf:A.array U8.t)
  (privk:A.array U8.t)
  (len:US.t)
  (msg:A.array U8.t)
  (#pprivk #pmsg:perm)
  (#buf0 #privk_seq #msg_seq:Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to buf full_perm buf0 `star`
     A.pts_to privk pprivk privk_seq `star`
     A.pts_to msg pmsg msg_seq)
    (fun _ -> exists_ (fun (buf1:Seq.seq U8.t) ->
      A.pts_to buf full_perm buf1 `star`
      A.pts_to privk pprivk privk_seq `star`
      A.pts_to msg pmsg msg_seq `star`
      pure (buf1 `Seq.equal` spec_ed25519_sign privk_seq msg_seq)))

(* DICE hash constants *)

assume
val dice_hash_alg : alg_t

let dice_digest_len : US.t = digest_len dice_hash_alg

assume 
val dice_digest_len_is_hashable 
  : is_hashable_len dice_digest_len

assume 
val dice_digest_len_is_hkdf_ikm
  : valid_hkdf_ikm_len dice_digest_len

assume
val is_hashable_len_32
  : is_hashable_len 32sz
