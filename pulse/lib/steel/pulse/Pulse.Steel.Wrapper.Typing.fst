module Pulse.Steel.Wrapper.Typing

open FStar.Reflection.V2
open Pulse.Reflection.Util

module RT = FStar.Reflection.Typing

let return_stt_typing _ _ _ = admit ()
let return_stt_noeq_typing _ _ _ = admit ()
let return_stt_atomic_typing _ _ _ = admit ()
let return_stt_atomic_noeq_typing _ _ _ = admit ()
let return_stt_ghost_typing _ _ _ = admit ()
let return_stt_ghost_noeq_typing _ _ _ = admit ()

let while_typing _ _ _ = admit ()

let par_typing _ _ _ _ _ _ _ _ _ = admit ()

let exists_inversion _ = admit ()
let elim_exists_typing _ _ _ = admit ()
let intro_exists_typing _ _ _ = admit ()
let intro_exists_erased_typing _ _ _ = admit ()

let stt_admit_typing _ _ _ = admit ()
let stt_atomic_admit_typing _ _ _ = admit ()
let stt_ghost_admit_typing _ _ _ = admit ()

let rewrite_typing _ _ _ = admit ()
let with_local_typing _ _ _ _ _ _ _ = admit ()
