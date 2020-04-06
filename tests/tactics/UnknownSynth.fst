(*
   Copyright 2008-2018 Microsoft Research

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
module UnknownSynth

open FStar.Tactics

(* We cannot determine the type of `x` a-priori, so this should fail
 * before running. Currently it runs and fails, we should fix that. *)
[@expect_failure]
let x = synth_by_tactic (fun () -> exact (`42))

(* These are fine *)
let y : int = synth_by_tactic (fun () -> exact (`42))
let z = synth_by_tactic #int (fun () -> exact (`42))
