module EverCrypt.Ed25519
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

/// From Lib.IntTypes.size_t
inline_for_extraction noextract [@@noextract_to "krml"]
let size_t = U32.t

/// From Lib.IntTypes.max_size_t
noextract [@@noextract_to "krml"]
let max_size_t = pow2 32 - 1

/// From Spec.Ed25519.sign
noextract [@@noextract_to "krml"]
val spec_ed25519_sign: secret:Seq.lseq U8.t 32 -> msg:Seq.seq U8.t{Seq.length msg <= max_size_t} -> Seq.lseq U8.t 64

/// From EverCrypt.Ed25519.sign
///
/// NOTE: The original Low* type is underspecified, since it does not
/// expect the private_key and msg inputs to be disjoint. That's
/// fine, since here in Pulse we only care about pairwise disjoint
/// inputs and outputs.
val sign:
    signature:A.larray U8.t 64
  -> p_private_key: perm
  -> v_private_key: Ghost.erased (Seq.seq U8.t)
  -> private_key:A.larray U8.t 32
  -> msg_len:size_t
  -> p_msg: perm
  -> v_msg: Ghost.erased (Seq.seq U8.t)
  -> msg:A.larray U8.t (U32.v msg_len) ->
  stt (squash (Seq.length v_private_key == 32 /\ Seq.length v_msg == U32.v msg_len))
    (requires
      (exists* v_signature . A.pts_to signature v_signature) **
      A.pts_to private_key #p_private_key v_private_key **
      A.pts_to msg #p_msg v_msg
    )
    (ensures fun _ ->
      A.pts_to signature (spec_ed25519_sign v_private_key v_msg) **
      A.pts_to private_key #p_private_key v_private_key **
      A.pts_to msg #p_msg v_msg
    )

/// From Spec.Ed25519
noextract [@@noextract_to "krml"]
val spec_ed25519_verify: public:Seq.lseq U8.t 32 -> msg:Seq.seq U8.t{Seq.length msg <= max_size_t} -> signature:Seq.lseq U8.t 64 -> bool

/// From EverCrypt.Ed25519.verify
///
/// Similarly to `sign`, the original Low* type is underspecified:
/// since everything is read-only, nothing is required to be
/// disjoint. That's fine here in Pulse, where we do require pairwise
/// disjointness.
val verify:
    p_public_key: perm
  -> v_public_key: Ghost.erased (Seq.seq U8.t)
  -> public_key:A.larray U8.t 32
  -> msg_len:size_t
  -> p_msg: perm
  -> v_msg: Ghost.erased (Seq.seq U8.t)
  -> msg:A.larray U8.t (U32.v msg_len)
  -> p_signature: perm
  -> v_signature: Ghost.erased (Seq.seq U8.t)
  -> signature:A.larray U8.t 64 ->
  stt bool
    (requires
      A.pts_to public_key #p_public_key v_public_key **
      A.pts_to msg #p_msg v_msg **
      A.pts_to signature #p_signature v_signature
    )
    (ensures fun b ->
      pure (
        Seq.length v_public_key == 32 /\
        Seq.length v_msg == U32.v msg_len /\
        Seq.length v_signature == 64 /\
        b == spec_ed25519_verify v_public_key v_msg v_signature
      ) **
      A.pts_to public_key #p_public_key v_public_key **
      A.pts_to msg #p_msg v_msg **
      A.pts_to signature #p_signature v_signature
    )
