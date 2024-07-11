module EverCrypt.HMAC
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

module H = EverCrypt.Hash.Incremental

/// From EverCrypt.HMAC.is_supported_alg
// val is_supported_alg: H.hash_alg -> bool

// inline_for_extraction noextract
// let supported_alg = a:H.hash_alg{ is_supported_alg a }

/// From Spec.Hash.Definitions.block_length
noextract [@@noextract_to "krml"]
val block_length: H.hash_alg -> pos

/// From Spec.Agile.HMAC
noextract [@@noextract_to "krml"]
let keysized (a:H.hash_alg) (l:nat) =
  l `H.less_than_max_input_length` a &&
  l + block_length a < pow2 32

val sha2_256_is_keysized : squash (keysized Spec.Hash.Definitions.sha2_256 32)

/// From Spec.Agile.HMAC
noextract [@@noextract_to "krml"]
val spec_hmac:
  a: H.hash_alg ->
  key: Seq.seq U8.t ->
  data: Seq.seq U8.t ->
  Pure (Seq.lseq U8.t (H.hash_length a))
    (requires keysized a (Seq.length key) /\
      (Seq.length data + block_length a) `H.less_than_max_input_length` a)
    (ensures fun _ -> True)

let compute_st_spec_hmac_intro : squash (pow2 32 < pow2 61) = // needed by compute_st
  assert_norm (pow2 32 < pow2 61)

/// From EverCrypt.HMAC.compute_st
///
/// NOTE: The original Low* definition is underspecified, since it
/// allows some buffers to not be disjoint. That's fine, since here in
/// Pulse we only care about pairwise disjoint inputs and outputs.
inline_for_extraction noextract
let compute_st (a: H.hash_alg) =
  tag: A.array U8.t {A.length tag == H.hash_length a} ->
  key: A.array U8.t { keysized a (A.length key) } ->
  p_key: perm ->
  v_key: Ghost.erased (Seq.seq U8.t) ->
  keylen: U32.t{ U32.v keylen = A.length key } ->
  // Can we have max_input_length a instead of pow2 32? (original comment in EverCrypt.HMAC)
  data: A.array U8.t { A.length data + block_length a < pow2 32 } ->
  p_data: perm ->
  v_data: Ghost.erased (Seq.seq U8.t) ->
  datalen: U32.t{ U32.v datalen = A.length data } ->
  stt (squash (Seq.length v_key == A.length key /\ Seq.length v_data == A.length data))
  (requires
    (exists* v_tag . A.pts_to tag v_tag) **
    A.pts_to key #p_key v_key **
    A.pts_to data #p_data v_data
  )
  (ensures fun _ ->
    A.pts_to tag (spec_hmac a v_key v_data) **
    A.pts_to key #p_key v_key **
    A.pts_to data #p_data v_data
  )

/// From EverCrypt.HMAC.compute
val compute: a: H.hash_alg -> compute_st a
