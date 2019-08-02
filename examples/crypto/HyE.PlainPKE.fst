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
module HyE.PlainPKE

open HyE.RSA
open HyE.Ideal

type t = HyE.AE.key // This should be abstract
type r = HyE.RSA.plain

(* two pure functions, never called when ideal *)
val repr:    p:t{not conf} -> Tot r
let repr t = HyE.AE.leak t       (* a pure function from t to RSA.plain *)

assume val coerce: x:r -> Tot (option (y:t)) //MK changed from t{repr y = x}
//let coerce t = Some t (* a partial function from RSA.plain to t *)
