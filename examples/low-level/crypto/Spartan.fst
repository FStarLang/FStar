module Spartan

open FStar.HyperStack.ST
open FStar.Buffer

type u8=FStar.UInt8.t

assume val keyExpansion:
  key:buffer u8 ->
  w:buffer u8 ->
  sb:buffer u8 -> Stack unit
  (requires (fun h -> live h key /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> modifies_1 w h0 h1))

assume val cipher:
  out:buffer u8 ->
  input:buffer u8 ->
  w:buffer u8 ->
  sb:buffer u8 -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sb))
  (ensures (fun h0 _ h1 -> modifies_1 out h0 h1))
