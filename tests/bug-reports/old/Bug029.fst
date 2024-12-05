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
module Bug029

(* Some tests for heterogenous equality *)

val f1 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b == g a})) -> x:'a -> r:'b{r == g x}
let f1 g h x = h x


val f2 : g:('a -> Tot 'b) -> x:'a -> r:('b * 'b){r == (g x, g x)}
let f2 g x = (g x, g x)


val f3 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b == g a})) ->  x:'a -> r:('b * 'b){r == (g x, g x)}
let f3 g h x = (h x, h x)


(*  Unfortunately: (h x, h x) in the type is inferred to
    have type (b:'b{b == h x} * b:'b{b == h x}), which isn't the same as r; the types differ

    val f4 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b == g a})) ->  x:'a -> Tot (r:('b * 'b){r == (h x, h x)}

    Need to write the type instantiations explicitly.
*)
val f4 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b == g a})) ->  x:'a -> Tot (r:('b * 'b){r == MkTuple2 #'b #'b (h x) (g x)})
let f4 g h x = (h x, h x)

(* Or, alternatively, don't use heterogenous equality. *)
val f4' : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b = g a})) ->  x:'a -> Tot (r:('b * 'b){r=(h x, h x)})
let f4' g h x = (h x, h x)

val f5 : g:('a -> Tot 'a) -> h:(a:'a -> Tot (b:'b{b == g a})) ->  x:'a -> Tot (r:('b * 'b){MkTuple2._1 r = MkTuple2._2 r})
let f5 g h x = (h x, h x)

val f6 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b = g a})) ->  x:'a -> r:('b * 'b){fst r = snd r}
let f6 g h x = (h x, h x)

val f7 : g:('a -> Tot 'b) -> h:(a:'a -> Tot (b:'b{b = g a})) ->  x:'a -> r:('b * 'b){fst r = snd r}
let f7 g h x = (g x, h x)
