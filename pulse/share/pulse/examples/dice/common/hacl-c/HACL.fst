module HACL

let alg_t = (a: EverCrypt.HMAC.supported_alg { US.fits_u32 })

let digest_len a = US.uint32_to_sizet (EverCrypt.Hash.Incremental.hash_len a)

let is_hashable_len x =
  (US.v x < pow2 32) /\
  (forall (a: alg_t) .
    EverCrypt.HMAC.keysized a (US.v x))

let is_signable_len x =
  US.v x <= EverCrypt.Ed25519.max_size_t

let valid_hkdf_lbl_len _ = True // FIXME: where is this used?

let valid_hkdf_ikm_len _ = True // FIXME: where is this used?

let spec_hash
  a s
= EverCrypt.Hash.Incremental.spec_hash a s

// inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn hacl_hash0
              (alg:alg_t)
              (src_len: hashable_len)
              (src:A.larray U8.t (US.v src_len))
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (#psrc:perm)
              (#src_seq #dst_seq:erased (Seq.seq U8.t))
requires
    (A.pts_to dst dst_seq **
     A.pts_to src #psrc src_seq)
ensures
       A.pts_to src #psrc src_seq **
       A.pts_to dst (spec_hash alg src_seq)
{
  A.pts_to_len src;
  EverCrypt.AutoConfig2.init ();
  EverCrypt.Hash.Incremental.hash alg dst src psrc src_seq (US.sizet_to_uint32 src_len);
  drop_ EverCrypt.AutoConfig2.initialized
}
```

let hacl_hash = hacl_hash0

// let hacl_hash alg src_len src dst #psrc #src_seq = hacl_hash0 alg src_len src dst #psrc #src_seq

let spec_hmac
  a k m
= if EverCrypt.HMAC.keysized a (Seq.length k) &&
     (Seq.length m + EverCrypt.HMAC.block_length a) `EverCrypt.Hash.Incremental.less_than_max_input_length` a
  then EverCrypt.HMAC.spec_hmac a k m 
  else Seq.create (US.v (digest_len a)) 0uy (* dummy *)

// inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn hacl_hmac0 (alg:alg_t)
              (dst:A.larray U8.t (US.v (digest_len alg)))
              (key:A.array U8.t)
              (key_len: hashable_len { US.v key_len == A.length key })
              (msg:A.array U8.t)
              (msg_len: hashable_len { US.v msg_len == A.length msg })
              (#pkey #pmsg:perm)
              (#dst_seq:erased (Seq.seq U8.t))
              (#key_seq:erased (Seq.seq U8.t))
              (#msg_seq:erased (Seq.seq U8.t))
requires
    (A.pts_to dst dst_seq **
     A.pts_to key #pkey key_seq **
     A.pts_to msg #pmsg msg_seq)
ensures    (
       A.pts_to key #pkey key_seq **
       A.pts_to msg #pmsg msg_seq **
       A.pts_to dst (spec_hmac alg key_seq msg_seq))
{
  let prf = EverCrypt.HMAC.compute alg dst key pkey key_seq (US.sizet_to_uint32 key_len) msg pmsg msg_seq (US.sizet_to_uint32 msg_len);
  rewrite (A.pts_to dst (EverCrypt.HMAC.spec_hmac alg key_seq msg_seq))
    as (A.pts_to dst (spec_hmac alg key_seq msg_seq))
}
```

let hacl_hmac = hacl_hmac0

// let hacl_hmac alg dst key key_len msg msg_len #pkey #pmsg #dst_seq #key_seq #msg_seq =
//  hacl_hmac0 alg dst key key_len msg msg_len #pkey #pmsg #dst_seq #key_seq #msg_seq

let spec_ed25519_verify
  pubk hdr sig
= Seq.length pubk == 32 /\
  Seq.length hdr <= EverCrypt.Ed25519.max_size_t /\
  Seq.length sig == 64 /\
  EverCrypt.Ed25519.spec_ed25519_verify pubk hdr sig == true

// inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn ed25519_verify0
  (pubk:A.larray U8.t (US.v v32us))
  (hdr:A.array U8.t)
  (hdr_len:signable_len { US.v hdr_len == A.length hdr })
  (sig:A.larray U8.t 64)
  (#ppubk #phdr #psig:perm)
  (#pubk_seq #hdr_seq #sig_seq:erased (Seq.seq U8.t))
requires
    (A.pts_to pubk #ppubk pubk_seq **
     A.pts_to hdr #phdr hdr_seq **
     A.pts_to sig #psig sig_seq)
returns res: bool
ensures
    (
      A.pts_to pubk #ppubk pubk_seq **
      A.pts_to hdr #phdr hdr_seq **
      A.pts_to sig #psig sig_seq **
      pure (res == true <==> spec_ed25519_verify pubk_seq hdr_seq sig_seq)
    )
{
  EverCrypt.Ed25519.verify ppubk pubk_seq pubk (US.sizet_to_uint32 hdr_len) phdr hdr_seq hdr psig sig_seq sig
}
```

let ed25519_verify = ed25519_verify0

// let ed25519_verify pubk hdr hdr_len sig #ppubk #phdr #psig #pubk_seq #hdr_seq #sig_seq =
// ed25519_verify0 pubk hdr hdr_len sig #ppubk #phdr #psig #pubk_seq #hdr_seq #sig_seq

let spec_ed25519_sign
  privk msg
= if Seq.length privk = 32 && Seq.length msg <= EverCrypt.Ed25519.max_size_t
  then EverCrypt.Ed25519.spec_ed25519_sign privk msg
  else Seq.empty // dummy

// inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn ed25519_sign0
  (buf:A.larray U8.t 64)
  (privk:A.larray U8.t (US.v v32us))
  (len:US.t { US.v len < pow2 32 })
  (msg:A.larray U8.t (US.v len))
  (#pprivk #pmsg:perm)
  (#buf0 #privk_seq #msg_seq:erased (Seq.seq U8.t))
requires
    (A.pts_to buf buf0 **
     A.pts_to privk #pprivk privk_seq **
     A.pts_to msg #pmsg msg_seq)
ensures
    (exists* (buf1:Seq.seq U8.t).
      A.pts_to buf buf1 ** 
      A.pts_to privk #pprivk privk_seq **
      A.pts_to msg #pmsg msg_seq **
      pure (buf1 `Seq.equal` spec_ed25519_sign privk_seq msg_seq))
{
  A.pts_to_len privk;
  A.pts_to_len msg;
  let prf = EverCrypt.Ed25519.sign buf pprivk privk_seq privk (US.sizet_to_uint32 len) pmsg msg_seq msg;
  ()
}
```

let ed25519_sign = ed25519_sign0

// let ed25519_sign buf privk len msg #pprivk #pmsg #buf0 #privk_seq #msg_seq =
//  ed25519_sign0 buf privk len msg #pprivk #pmsg #buf0 #privk_seq #msg_seq

assume val dice_hash_alg1 (_: unit) : alg_t

let dice_hash_alg0 _ = dice_hash_alg1 ()

inline_for_extraction noextract [@@noextract_to "krml"]
let dice_digest_len0 = 32sz // FIXME: this is taken from previously handwritten hacl.rs

assume val dice_digest_len_spec : squash (
  is_hashable_len (digest_len dice_hash_alg) /\
  dice_digest_len0 == digest_len dice_hash_alg
)

let dice_digest_len = dice_digest_len0
