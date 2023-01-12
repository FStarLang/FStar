(*
   Copyright 2021 Microsoft Research

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
module Steel.ST.Loops
module US = FStar.SizeT
open Steel.ST.Util

(* This module provides some common iterative looping combinators *)

let nat_at_most (f:US.t)
  = x:nat{ x <= US.v f }

let u32_between (s f:US.t)
  = x:US.t { US.v s <= US.v x /\ US.v x < US.v f}

/// for_loop: for (i = start; i < finish; i++) inv { body i }
val for_loop (start:US.t)
             (finish:US.t { US.v start <= US.v finish })
             (inv: nat_at_most finish -> vprop)
             (body:
                    (i:u32_between start finish ->
                          STT unit
                          (inv (US.v i))
                          (fun _ -> inv (US.v i + 1))))
  : STT unit
      (inv (US.v start))
      (fun _ -> inv (US.v finish))

/// while_loop: while (cond()) { body () }
val while_loop (inv: bool -> vprop)
               (cond: (unit -> STT bool
                                     (exists_ inv)
                                     (fun b -> inv b)))
               (body: (unit -> STT unit
                                     (inv true)
                                     (fun _ -> exists_ inv)))
  : STT unit
    (exists_ inv)
    (fun _ -> inv false)
