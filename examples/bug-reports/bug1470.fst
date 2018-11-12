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
module Bug1470

val length : list 'a -> Dv nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

assume val aux (n:int) :Dv nat

let length1 (n:int) :Dv nat = 1 + aux n

(*
 * From Kremlin test suite
 *)
open FStar.ST

assume val bar (_:unit) :St (x:int{x == 42})

assume val foo (x:int) :Pure int (requires True) (ensures (fun r -> r == x))

#set-options "--max_fuel 0 --max_ifuel 0"
let test () :St unit =
  let y = foo (bar ()) in
  assert (y == 42)
