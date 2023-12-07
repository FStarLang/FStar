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
module FStar.DM4F.StMap

open FStar.DM4F.ST
open FStar.Map

irreducible type t (a:eqtype) : Type = int
type t0 = Map.t int int

let eq_int : eqtype = int

let state = (Map.t int int)
total  new_effect {
  STMAP  : a:Type -> Effect
  with repr     = st state
     ; bind     = bind_st state
     ; return   = return_st state
     ; get      = get state
     ; put      = put state
}
