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
module Bug367

val f : int -> Tot unit
let f = function x | _ -> ()
(*
Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Invalid_argument("for_all2: Different_list_size")
*)

(*
val f : int * int -> Tot unit
let f p = match p with
| x,y
| x,_ -> ()
Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Invalid_argument("for_all2: Different_list_size")
*)

(*
val f : int -> Tot unit
let f = function x | y -> ()
/home/hritcu/Projects/fstar/pub/examples/bug-reports/bug367.fst(22,16-22,22) : Error
Each branch of this pattern binds different variables: x;
y
*)
