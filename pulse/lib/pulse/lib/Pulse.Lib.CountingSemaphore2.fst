(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.CountingSemaphore2
#lang-pulse
module B = Pulse.Lib.Box
module CInv = Pulse.Lib.CancellableInvariant

noeq type sem (p: slprop) : Type0 = {
  counter: B.box U32.t;
  permit_tank: Tank.tank (U32.v sem_max);
  i: CInv.cinv;
}

(** Full invariant *)
let sem_inv (p: slprop) (counter: B.box U32.t) (permit_tank: Tank.tank (U32.v sem_max)) : slprop =
  exists* (n: U32.t).
    counter |-> n **
    replicate p (U32.v n) **
    Tank.owns permit_tank (U32.v n)