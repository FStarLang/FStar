module Pulse.C.Types.Array.Base
#lang-pulse
module SZ = FStar.SizeT

inline_for_extraction
let array_domain
  (n: Ghost.erased SZ.t)
: Tot eqtype
= (i: SZ.t { SZ.v i < SZ.v n })
