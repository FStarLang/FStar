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
module CCA2.Plain
open CCA2

(* private  *)type t = RSA.plain
type r = RSA.plain

(* two pure functions, never called when ideal *)
val repr:    t -> Tot r
let repr t = t       (* a pure function from t to RSA.plain *)

val coerce: x:r -> Tot (option (y:t{repr y = x}))
let coerce t = Some t (* a partial function from RSA.plain to t *)
