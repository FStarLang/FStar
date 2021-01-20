(*
   Copyright 2020 Microsoft Research

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
module TestFSharp

open FStar.IO

let t (a:Type) (b:Type) = list a

let test #a #b (f:t a b) : list a = f

(* 
	Examples from issue #1087
*)

val pass: #a:Type -> #b:Type -> #c:Type -> a -> b -> (a -> b -> c) -> c
let pass #a #b #c x y f = f x y

(* TODO: Only implicit arguments at the start of a function are erased, whereas the others are extracted to unit and obj 
         which makes extracted function unusable.
*)
val fail: #a:Type -> a -> #b:Type -> b -> #c:Type -> (a -> b -> c) -> c
let fail #a x #b y #c f = f x y

type fs0035 (a:Type) (n:nat) = a

