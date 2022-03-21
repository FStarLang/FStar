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
module Bug734

type dir =
| Bool | Int | Fun

let arg_type (d:dir) : Tot Type0 =
  match d with
  | Bool   -> bool
  | Int    -> int
  | Fun    -> int -> Tot int

let def_value (d:dir) : Tot (arg_type d) =
  match d with
  | Bool -> true
  | Int -> 42
  | Fun -> (fun (x:int) -> x)

let example_works = def_value Bool

let example_fails = def_value Fun 42

(*
Extracting module Bug
./bug.fst(20,20-20,36): Ill-typed application: application is (Bug.def_value Bug.Fun 42) 
 remaining args are 42
ml type of head is Obj.t
[..]
Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Failure("Ill-typed application: application is (Bug.def_value Bug.Fun 42) \n remaining args are 42\nml type of head is Obj.t\n")
*)
