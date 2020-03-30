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
module NegativeTests.ShortCircuiting

assume type bad_p : bool -> Type
val bad : x:int -> Tot (b:bool{bad_p b})
[@ (expect_failure [19])]
let rec bad x = true || bad (x-1)

val ff : unit -> Lemma (ensures False)
[@ (expect_failure [19])]
let ff u = ignore (false && (0 = 1))
