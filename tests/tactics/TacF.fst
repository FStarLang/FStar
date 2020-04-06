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
module TacF

open FStar.Tactics

(* Not exhaustive! But we're in TacF, so it's accepted *)
let tau i : TacF unit =
    match i with
    | 42 -> exact (`())

(* If we call it just right, it even works *)
let u : unit = synth_by_tactic (fun () -> assume_safe (fun () -> tau 42))

let foo (x:int) : Tac unit = exact (`())

[@expect_failure]
let test1 (a:Type) (x:a) : unit = _ by (foo x)

let test2 (a:Type) (x:a) : unit = _ by (assume_safe (fun () -> foo x))
