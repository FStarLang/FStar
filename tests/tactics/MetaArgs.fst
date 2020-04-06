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
module MetaArgs

open FStar.Tactics

(* Quick test for a meta arg *)
let test1 (#[exact (`42)] i : int) : int = i

let _ = assert (test1 == 42)


(* Testing that previous arguments are in-scope for the metaprogarm *)
let same_as (i:int) = exact (quote i)

(* By default, a diagonal function, but allows to be overriden *)
let diag (x:int) (#[same_as x] y:int) : int * int = (x, y)

let _ = assert (diag 42 #43 == (42, 43))
let _ = assert (diag 42     == (42, 42))
