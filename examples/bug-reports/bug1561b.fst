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
module Bug1561b

class a = {x : bool}

let t [| a |] : Tot Type = if x then ℤ else unit

type u = | A | B

let f_t [| _ : a |]  :  Tot Type = u → t → Tot t

instance ii : a = { x = true }

let f0 : f_t = fun l y → y

(* used to explode with an assertion failure *)
val test : unit -> unit
let test () : unit =
    let f : f_t = fun l y → y
    in ()

val f1 : f_t
let f1 = fun l y → y
