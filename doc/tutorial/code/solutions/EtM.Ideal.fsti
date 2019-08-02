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
module EtM.Ideal

val ind_cpa : bool

val uf_cma : b:bool{ ind_cpa ==> b }

let ind_cpa_rest_adv = uf_cma
(* well typed adversaries only submit ciphertext obtained using encrypt *)

let conf = ind_cpa

let auth = uf_cma
