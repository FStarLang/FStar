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
module TestGhost

open FStar.Ghost

//let f (x:erased int) = x + 1 //type-error; x is not an int

// val g: erased int -> Tot int
let g x = reveal x    //type-error: Erased is not a sub-effect of pure

//fine; having erased effects in specifications is ok
val h: x:erased int -> Pure (erased int) (requires (b2t (reveal x >= 0))) (ensures (fun y -> x == y))
let h x = x

//fine; having erased effects in specifications is ok
val i: x:erased int -> Pure int (requires (b2t (reveal x = 0))) (ensures (fun y -> x == hide y))
let i x = 0 //fine

//fine; having erased effects in specifications is ok
assume val j: x:erased int -> Pure int (requires (b2t (reveal x = 0)))
                                   (ensures (fun y -> x == hide y))
//let j x = 1 -- logical failure
