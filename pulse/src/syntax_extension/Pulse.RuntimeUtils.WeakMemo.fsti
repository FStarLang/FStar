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

module Pulse.RuntimeUtils.WeakMemo
open FStarC.Effect

(* A memo table with weak keys: an entry is dropped once its key is
   unreachable.  Keys are compared structurally, and physically equal keys
   are found without traversing them.  Returns the lookup and the update
   functions of a fresh table. *)
val create (#k #v : Type0) (_:unit)
  : ML ((k -> ML (option v)) & (k -> v -> ML unit))
