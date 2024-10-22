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
module Bug581

open FStar.All

//#set-options "--log_types --print_effect_args"

assume new type p: int -> Type0

assume val f: n:int{p n} -> int

//The three declarations below are equivalent and with all of them g fails to typecheck
//val g: unit -> int
//val g: unit -> ML int
//val g: unit -> ALL int (fun post _ -> forall a h. post a h)

//Inferred type and effect when no declaration is given; with it g typechecks
val g: unit -> ALL int (fun post _ -> p 0 /\ (forall a h. post a h))

let g () = f 0
