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
module Bug021

val constfun0 : bool -> int -> Tot bool
let constfun0 x k = x

let ftrue0 = constfun0 true

val test0 : int -> Tot unit
let test0 x = assert (ftrue0 x = true)

val constfun : 'a -> 'b -> Tot 'a
let constfun x k = x

val ftrue : 'b -> Tot bool
let ftrue x = constfun true x

val test : int -> Tot unit
let test x = assert (ftrue x = true)

val my_override : ('a -> Tot 'b) -> 'a -> 'b -> Tot ('a -> Tot 'b)
let my_override f k x k' = if k = k' then x else f k'

val fmostlytrue : int -> Tot bool
let fmostlytrue x = my_override (my_override ftrue 1 false) 3 false x

val override_example1 : unit -> Lemma
      (ensures (fmostlytrue 0 = true))
let override_example1 () = ()

val override_example2 : unit -> Lemma
      (ensures (fmostlytrue 1 = false))
let override_example2 () = ()

val override_example3 : unit -> Lemma
      (ensures (fmostlytrue 2 = true))
let override_example3 () = ()

val override_example4 : unit -> Lemma
      (ensures (fmostlytrue 3 = false))
let override_example4 () = ()
