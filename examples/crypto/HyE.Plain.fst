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
module HyE.Plain

open Platform.Bytes
open CoreCrypto
open HyE.Ideal


abstract type t = bytes

assume Plain_hasEq: hasEq t

type r = bytes

(* two pure functions, never called when ideal *)
abstract val repr:    p:t{not conf} -> Tot r
let repr t = t       (* a pure function from t to RSA.plain *)

abstract val coerce: x:r -> Tot t //(y:t{y = x}))
let coerce t =t (* a function from r to t *)

abstract val length: p:t -> Tot nat
let length p = length p
