module Crypto.Symmetric.Poly1305.Parameters

(* Standard platform integer size *)
inline let platform_size : pos = 64
(* Integer size after multiplication *)
inline let platform_wide : pos = 64
(* Canonical number of limbs *)
inline let norm_length : pos = 5
inline let nlength : FStar.UInt32.t = 5ul
(* Canonical number of bytes *)
inline let bytes_length : pos = 17
inline let blength : FStar.UInt32.t = assert_norm (17 < pow2 32); 17ul
(* Representation template *)
inline val templ: nat -> Tot pos
inline let templ = fun x -> 26
