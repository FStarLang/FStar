module EverCrypt.AutoConfig2
open Pulse.Lib.Pervasives

/// See https://github.com/hacl-star/hacl-star/blob/59723f7dde13bd7b7eb90491f1385b4e3ee2904f/providers/evercrypt/fst/EverCrypt.Hash.Incremental.fst#L292-L294

noextract [@@noextract_to "krml"]
val initialized: vprop

val init: unit -> stt unit
  (requires emp)
  (ensures fun _ -> initialized)
