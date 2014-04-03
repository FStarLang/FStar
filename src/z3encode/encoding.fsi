(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module Microsoft.FStar.Z3Encoding.Encoding
open Absyn

(* No-ops *)
val init_state : unit -> unit
val clear : unit -> unit
val finish : (unit -> unit)
val clear_gamma_cache : (unit -> unit)

type formula = typ
val query : (Tcenv.env -> formula -> bool)
val query_equality: (Tcenv.env -> Absyn.exp -> Absyn.exp -> bool * option<Absyn.exp'>)
