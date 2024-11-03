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
open Pulse.Lib.ConditionVarWithCodes
module CV = Pulse.Lib.ConditionVarWithCodes
////////////////////////////////////////////////////////////////
//Using condition vars directly with slprop2 slprops
////////////////////////////////////////////////////////////////

let code : CV.code = {
  t = slprop2_base;
  emp = down2 emp;
  up = (fun x -> up2_timeless x; up2 x);
  laws = ()
}

let code_of (p:slprop2) : CV.codeable code p = {
  c = down2 p;
  laws = ()
}

let cvar_t = CV.cvar_t code

let inv_name (c:cvar_t) = CV.inv_name c

let send (cv:cvar_t) (p:slprop) : slprop = CV.send cv p

let recv (cv:cvar_t) (p:slprop) : slprop = CV.recv cv p

let create (p:slprop2)
: stt cvar_t emp (fun b -> send b p ** recv b p)
= CV.create p (code_of p)

let signal (cv:cvar_t) (#p:slprop)
: stt unit (send cv p ** p) (fun _ -> emp)
= CV.signal cv #p

let wait (cv:cvar_t) (#p:slprop)
: stt unit (recv cv p) (fun _ -> p)
= CV.wait cv #p

let split (cv:cvar_t) (#p #q:slprop2)
: stt_ghost unit (add_inv emp_inames (inv_name cv))
  (recv cv (p ** q)) (fun _ -> recv cv p ** recv cv q)
= CV.split cv #p #q (code_of p) (code_of q)
