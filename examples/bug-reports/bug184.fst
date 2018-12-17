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
module Bug184
type refl (a:Type) : a -> a -> Type =
  | Refl : x:a -> refl a x x

type refl' : int -> int -> Type = refl int

val foo : e:int -> e':int -> s: refl' e e' -> Tot unit
let foo e e' s = match s with
  | Refl _ -> ()
