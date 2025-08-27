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

module Pulse.Lib.WhileLoop
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core


fn rec while_loop'
  (inv:bool -> slprop)
  (cond:unit -> stt bool (exists* x. inv x) (fun b -> inv b))
  (body:unit -> stt unit (inv true) (fun _ -> exists* x. inv x))
  norewrite
  requires exists* x. inv x
  ensures inv false
{
  let b = cond ();
  if b {
     body ();
     while_loop' inv cond body;
  }
}


let while_loop inv cond body = 
  while_loop' inv (fun _ -> cond) (fun _ -> body)


fn rec nu_while_loop
  (inv:slprop)
  (post:bool -> slprop)
  (cond:unit -> stt bool inv (fun b -> post b))
  (body:unit -> stt unit (post true) (fun _ -> inv))
  requires inv
  ensures post false
{
  let b = cond ();
  if b {
     body ();
     nu_while_loop inv post cond body;
  }
}
