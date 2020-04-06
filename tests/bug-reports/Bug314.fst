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
module Bug314

open FStar.All
open FStar.String
open FStar.IO

(* two events, recording genuine requests and responses *)

type lnat = nat


val escape : lnat -> Tot nat
let escape l = l


assume new type request : string -> Type
assume new type response : string -> string -> Type

(* the meaning of MACs, as used in RPC *)

type reqresp (msg:string) = (exists s. request s)
