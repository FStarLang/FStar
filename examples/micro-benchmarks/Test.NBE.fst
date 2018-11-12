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
module Test.NBE
// [iota; zeta; simplify; primops; delta_attr [`%va_qattr]; delta_only normal_steps]
unfold let normal (#a:Type) (x:a) : a = norm [primops; nbe] x
val x : bool
let x = normal (true && false)

val easy : n:nat -> Lemma (n + 2 = n + normal (1 + 1))
let easy n = ()

let rec append_int (x y:list int) : Tot (list int) =
  match x with
  | [] -> y
  | hd::tl -> hd::append_int tl y


let test1 =
  assert (norm [primops; delta; zeta; nbe] (append_int [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])


let rec append (#a:Type) (x y:list a) : Tot (list a) =
  match x with
  | [] -> y
  | hd::tl -> hd::append tl y


let test2 =
  assert (norm [primops; delta; zeta; nbe] (append [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])

let test3 =
  assert (norm [primops; delta; zeta; nbe] (List.append [1;2;3;4;5;6;7] [8;9])
          = [1;2;3;4;5;6;7;8;9])

#set-options "--debug_level NBE --debug Test.NBE --max_fuel 0"
