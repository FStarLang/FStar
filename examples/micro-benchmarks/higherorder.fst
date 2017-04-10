(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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


module HO

val f1 : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
let f1 g h x = (g x, h x)

(* val f2 : g:('a -> Tot 'b) -> h:('a -> Tot 'b){forall (a:'a). g a = h a} -> 'a -> r:('b * 'b){fst r = snd r} *)
(* let f2 g h x = (g x, h x) *)

val f3 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b = g a})) -> 'a -> r:('b * 'b){fst r = snd r}
let f3 g h x = (g x, h x)
