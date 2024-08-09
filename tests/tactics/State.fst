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
module State

open FStar.Tactics.V2

let x : int = synth (fun () -> lset "myint" 1;
                               let y : int = lget "myint" in
                               exact (quote y))

let _ = assert (x == 1)

// Can't type 1 as a bool
[@@expect_lax_failure]
let y : int = synth (fun () -> lset "myint" 1;
                               let y : bool = lget "myint" in
                               exact (quote y))
