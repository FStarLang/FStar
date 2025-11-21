(*
   Copyright 2024 Microsoft Research

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
module Pulse.Lib.Par
#lang-pulse
open Pulse.Lib.Core
open Pulse.Lib.Send
open PulseCore.Observability

fn par (#preL: slprop) #postL #preR #postR
  {| is_send preL, is_send postL, is_send preR, is_send postR |}
  (f:unit -> stt unit preL (fun _ -> postL))
  (g:unit -> stt unit preR (fun _ -> postR))
  requires preL ** preR
  ensures postL ** postR
