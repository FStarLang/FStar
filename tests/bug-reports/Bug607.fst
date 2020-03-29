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
module Bug607

// Not ok
type my_type (a:Type) (b:Type) = list (a * b)

val f: my_type int int -> unit
let f x = let rec helper (x: my_type int int) = x in ()

// Ok
type my_type2 (a:Type) (b:Type) = list (a * b)

val f2: my_type2 int int -> unit
let f2 x = let helper (x: my_type2 int int) = x in ()
