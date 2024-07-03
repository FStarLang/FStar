(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at


   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.InvToken

open Pulse.Lib.Pervasives

val token (i:iname) (p:vprop) : Type u#4

val witness (i:iname) (#p:vprop)
  : stt (token i p)
        (requires inv i p)
        (ensures fun _ -> emp)

val recall (#i:iname) (#p:vprop) (t:token i p)
  : stt unit
        (requires emp)
        (ensures fun _ -> inv i p)
