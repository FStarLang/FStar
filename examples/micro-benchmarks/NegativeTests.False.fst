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
module NegativeTests.False 
(* #284 *)
val foo : f:(unit -> Tot bool){f () = true}
          -> Tot (r:bool {r = f () /\ r = true})
let foo f = f ()
val bar : unit -> Pure bool (requires True) (ensures (fun _ -> False))
[@(expect_failure [19])]
let bar () = foo (fun x -> false)

(*#380*)
val f : p1:(True \/ True) -> p2:(True \/ True) -> Lemma (p1 = p2)
let f p1 p2 = ()
val absurd : unit -> Lemma False
[@expect_failure] // this raises 2 errors on 1-phase, and 4 on 2-phases
let absurd () = f (Left #_ #True T) (Right #True #_ T) //adding implicits to get 2 typing errors
