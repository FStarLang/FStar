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

module Pulse.Lib.ConditionVar
open Pulse.Lib.Pervasives

let cvar_t : Type0 = unit

let inv_name (c:cvar_t) : iname = admit()

let send (c:cvar_t) (p:slprop) : slprop = admit()

let recv (c:cvar_t) (p:slprop) : slprop = admit()

let create (p:slprop)
: stt cvar_t emp (fun b -> send b p ** recv b p)
= admit()

let signal (b:cvar_t) (#p:slprop)
: stt unit (send b p ** p) (fun _ -> emp)
= admit()

let wait (b:cvar_t) (#p:slprop)
: stt unit (recv b p) (fun _ -> p)
= admit()

let split (b:cvar_t) (#p #q:slprop)
: stt_ghost unit (add_inv emp_inames (inv_name b))
  (recv b (p ** q)) (fun _ -> recv b p ** recv b q)
= admit()
