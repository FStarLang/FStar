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
module Bug138


val foo : l:list int -> Tot int (decreases %[l;0])
val bar : l:list int -> Tot int (decreases %[l;1])
let rec foo l = match l with
    | [] -> 0
    | x::xs -> bar xs
and bar l = foo l


type arg =
  | Foo : arg
  | Bar : arg

val arg_precede : arg -> Tot nat
let arg_precede a =
  match a with
    | Foo -> 0
    | Bar -> 1

val foo_bar : a:arg -> l:list int -> Tot int (decreases %[l;arg_precede a])
let rec foo_bar a l =
  match a with
    | Foo ->
       (match l with
          | [] -> 0
          | x::xs -> foo_bar Bar xs)
    | Bar -> foo_bar Foo l
