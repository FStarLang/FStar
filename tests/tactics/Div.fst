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
module Div

open FStar.Tactics

let rec f0 (x : int) : Dv int = f0 x
let g0 (x : int) : Tac int = f0 x

(* Testing that a non-diverging example works *)
let rec f (x : int) : Dv int = 25
let g (x : int) : Tac int = f x
let _ = assert True by (let x = g 2 in trivial ())
