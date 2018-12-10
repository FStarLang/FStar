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
module Bug655

open FStar.All
open FStar.Heap

let ghost_one () : GTot int = 1

assume val g: (u:unit) -> St unit

let test (u:unit) : St unit
  = ghost_one (); //rightfully complains about int </: unit
    g(); // (used to crash extraction)
    ()

let test2 (u:unit) : St unit
  = let _ = ghost_one () in //rightfully complains about Ghost nat not being composable with ST
    g(); // (used to crash extraction)
    ()
