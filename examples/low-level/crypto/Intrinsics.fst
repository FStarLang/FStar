module Intrinsics


open FStar.Buffer
open FStar.UInt8


assume val aes128_load:
  key:buffer UInt8.t ->
  Stack unit
  (requires (fun h -> live h key))
  (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))


assume val aes128_enc:
  output:buffer t ->
  input:buffer t ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))


assume val aes128_dec:
  output:buffer t ->
  input:buffer t ->
  Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
