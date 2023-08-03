module HACL
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

let v32us : US.t = 32sz

let coerce (l:US.t) (s:erased (elseq U8.t l)) : erased (Seq.seq U8.t)
  = let s_ = reveal s in 
    hide s_

let coerce_refined (l:US.t) (s:erased (Seq.seq U8.t){Seq.length (reveal s) == US.v l}) : erased (elseq U8.t l)
  = let s_ = reveal s in 
    hide s_

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
              (src_len: hashable_len)
              (src:A.larray U8.t (US.v src_len))
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (#psrc:perm)
              (#src_seq #dst_seq:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to dst full_perm dst_seq **
     A.pts_to src psrc src_seq)
    (fun _ ->
       A.pts_to src psrc src_seq **
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
              (#dst_seq:erased (Seq.seq U8.t))
              (#key_seq:erased (Seq.seq U8.t))
              (#msg_seq:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to dst full_perm dst_seq **
     A.pts_to key pkey key_seq **
     A.pts_to msg pmsg msg_seq)
    (fun _ ->
       A.pts_to key pkey key_seq **
       A.pts_to msg pmsg msg_seq **
       A.pts_to dst full_perm (spec_hmac alg key_seq msg_seq))

assume
val spec_ed25519_verify (pubk hdr sig:Seq.seq U8.t) : prop 

assume
val ed25519_verify 
  (pubk:A.larray U8.t (US.v v32us))
  (hdr:A.array U8.t)
  (hdr_len:signable_len { US.v hdr_len == A.length hdr })
  (sig:A.larray U8.t 64)
  (#ppubk #phdr #psig:perm)
  (#pubk_seq:erased (elseq U8.t v32us))
  (#hdr_seq #sig_seq:erased (Seq.seq U8.t))
  : stt bool
    (A.pts_to pubk ppubk pubk_seq **
     A.pts_to hdr phdr hdr_seq **
     A.pts_to sig psig sig_seq)
    (fun _ ->
      A.pts_to pubk ppubk pubk_seq **
      A.pts_to hdr phdr hdr_seq **
      A.pts_to sig psig sig_seq **
      pure (spec_ed25519_verify pubk_seq hdr_seq sig_seq))

assume
val spec_ed25519_sign (privk msg:Seq.seq U8.t) : Seq.seq U8.t

assume
val ed25519_sign 
  (buf:A.array U8.t)
  (privk:A.larray U8.t (US.v v32us))
  (len:US.t)
  (msg:A.larray U8.t (US.v len))
  (#pprivk #pmsg:perm)
  (#buf0:erased (Seq.seq U8.t))
  (#privk_seq:erased (elseq U8.t v32us))
  (#msg_seq:erased (elseq U8.t len))
  : stt unit
    (A.pts_to buf full_perm buf0 **
     A.pts_to privk pprivk privk_seq **
     A.pts_to msg pmsg msg_seq)
    (fun _ -> exists_ (fun (buf1:Seq.seq U8.t) ->
      A.pts_to buf full_perm buf1 **
      A.pts_to privk pprivk privk_seq **
      A.pts_to msg pmsg msg_seq **
      pure (buf1 `Seq.equal` spec_ed25519_sign privk_seq msg_seq)))

(* DICE hash constants *)

assume
val dice_hash_alg : alg_t

let dice_digest_len : hashable_len = assume (is_hashable_len (digest_len dice_hash_alg)); digest_len dice_hash_alg

assume 
val dice_digest_len_is_hashable 
  : is_hashable_len dice_digest_len

assume 
val dice_digest_len_is_hkdf_ikm
  : valid_hkdf_ikm_len dice_digest_len

assume
val is_hashable_len_32
  : is_hashable_len v32us
