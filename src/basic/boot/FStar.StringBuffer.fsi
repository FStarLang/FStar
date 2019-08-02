(*
   Copyright 2008-2019 Microsoft Research

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
#light "off"
module FStar.StringBuffer
open FStar.All
open Prims
open FStar.BigInt

type t

//This is a **MUTABLE** string buffer
//Although each function here returns a `t` the buffer is mutated in place.

//The argument convention is chosen so that you can conveniently write code like:
// sb |> add "hello" |> add " world" |> add "!"


val create : FStar.BigInt.t -> t
val add: string -> t -> t
val contents: t -> string
val clear: t -> t
val output_channel: FStar.Util.out_channel -> t -> unit
