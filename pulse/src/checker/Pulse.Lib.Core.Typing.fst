(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Core.Typing

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
let with_localarray_typing _ _ _ _ _ _ _ _ = admit ()

let unit_non_informative_witness_typing _ = admit ()
let prop_non_informative_witness_typing _ = admit ()
let squash_non_informative_witness_typing _ _ = admit ()