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
module Unif

val comp : 'a:Type -> 'b:Type ->
           'a -> ('a -> 'a) -> ('a -> 'b -> 'a) -> 'a -> 'a
let comp j f g x =
  let ff a z = f (g z (f (f (g x z)))) in
  let gg = g (f x) in
  ff j (gg j)

(* Error message before and after normalization:

Expected expression of type "[Before:'b][After:'b]";
got expression "z" of type
"[Before:((fun 'a:Type 'b:Type => 'a) 'a 'b)][After:'a]"
*)
