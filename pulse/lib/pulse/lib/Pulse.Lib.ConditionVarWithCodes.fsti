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


module Pulse.Lib.ConditionVarWithCodes
open Pulse.Lib.Pervasives
//open Pulse.Lib.Codeable

noeq
type code : Type u#4 = {
  t    : Type u#2;
  emp  : t;
  up   : t -> slprop;
  laws : squash ( up emp == Pulse.Lib.Pervasives.emp )
}

class codeable (code:code) (v:slprop) = {
  c : code.t;
  laws : squash (code.up c == v)
}

val cvar_t (c:code) : Type0

val inv_name #c (cv:cvar_t c) : iname

val send #c (cv:cvar_t c) (p:slprop) : slprop

val recv #c (cv:cvar_t c) (p:slprop) : slprop

val create #c (p:slprop) (pf: codeable c p)
: stt (cvar_t c) emp (fun b -> send b p ** recv b p)

val signal #c (cv:cvar_t c) (#p:slprop)
: stt unit (send cv p ** p) (fun _ -> emp)

val wait #c (cv:cvar_t c) (#p:slprop)
: stt unit (recv cv p) (fun _ -> p)

val split #c (cv:cvar_t c) (#p #q:slprop) (cq:codeable c p) (cr:codeable c q)
: stt_ghost unit (add_inv emp_inames (inv_name cv))
  (recv cv (p ** q)) (fun _ -> recv cv p ** recv cv q)



val cvinv #c (cv:cvar_t c) (p:slprop) : slprop

val dup_cvinv #c (cv:cvar_t c) (#p:slprop)
: stt_ghost unit emp_inames (cvinv cv p) (fun _ -> cvinv cv p ** cvinv cv p)

val send_core #c (cv:cvar_t c) : slprop

val decompose_send #c (cv:cvar_t c) (p:slprop)
: stt_ghost unit emp_inames (send cv p) (fun _ -> cvinv cv p ** send_core cv)

val recompose_send #c (cv:cvar_t c) (p:slprop)
: stt_ghost unit emp_inames (cvinv cv p ** send_core cv) (fun _ -> send cv p)

val recv_core #c (cv:cvar_t c) (q:slprop)
: slprop

val decompose_recv #c (cv:cvar_t c) (p:slprop)
: stt_ghost unit emp_inames 
  (recv cv p) (fun _ ->  (exists* q. cvinv cv q) ** recv_core cv p)
  
val recompose_recv #c (cv:cvar_t c) (p:slprop) (#q:_)
: stt_ghost unit emp_inames
  (cvinv cv q ** recv_core cv p) (fun _ -> recv cv p)
