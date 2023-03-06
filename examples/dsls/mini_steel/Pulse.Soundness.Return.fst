module Pulse.Soundness.Return

open FStar.Reflection
open Refl.Typing
module RT = Refl.Typing

let return_stt_typing _ _ _ = admit ()
let return_stt_noeq_typing _ _ _ = admit ()
let return_stt_atomic_typing _ _ _ = admit ()
let return_stt_atomic_noeq_typing _ _ _ = admit ()
let return_stt_ghost_typing _ _ _ = admit ()
let return_stt_ghost_noeq_typing _ _ _ = admit ()
