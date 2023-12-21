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

module Pulse.Lib.SpinLock
open Pulse.Lib.Core

val lock (p:vprop) : Type u#0

val new_lock
        (p:vprop)
  : stt (lock p)
        (requires p)
        (ensures (fun _ -> emp))

val acquire
        (#p:vprop)
        (l:lock p)
  : stt unit 
        (requires emp)
        (ensures (fun _ -> p))

val release
        (#p:vprop)
        (l:lock p)
  : stt unit
        (requires p)
        (ensures (fun _ -> emp))