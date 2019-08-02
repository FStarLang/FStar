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
module Unit1.Projectors1
open FStar.BaseTypes

type t = 
  | T : x:int -> y:nat -> t

val f : t:t -> Tot int
let f t = t.x

type s = 
  | S : x:bool -> y:nat -> s

let g s : bool = s.x

type u = {x:char; y:int} 
let h u : char = u.x

type v = 
  | V : field1:int -> field2:nat -> v
