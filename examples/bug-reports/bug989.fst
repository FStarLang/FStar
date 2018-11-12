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
module Bug989

let rec g (n:nat) =
  if n = 0 then true
  else g (n - 1)

#set-options "--initial_fuel 0 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
//#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let foo = assert (g 0 == true)


type t =
 | A
 | B

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 1"
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let f (x:t) =
  match x with
  | A -> ()
  | B -> ()
