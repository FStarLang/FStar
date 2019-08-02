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
module Bug577

type step : int -> Type =

noeq type multi (r:int -> Type) : int -> Type =
| Multi_step : x:int -> r x -> multi r x

val aux : e:int -> step e -> Tot bool
let aux e h = magic()

val steps_preserves_red : e:int -> b:multi step e -> Tot bool
let steps_preserves_red e h =
  match h with
  | Multi_step _ xx -> aux e xx
