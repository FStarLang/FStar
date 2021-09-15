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
module Steel.Loops
open Steel.Effect.Common
open Steel.Effect
module U32 = FStar.UInt32

(* This module provides some common iterative looping combinators *)

let nat_at_most (f:U32.t)
  = x:nat{ x <= U32.v f }

let u32_between (s f:U32.t)
  = x:U32.t { U32.v s <= U32.v x /\ U32.v x < U32.v f}

/// for_loop: for (i = start; i < finish; i++) inv { body i }
val for_loop (start:U32.t)
             (finish:U32.t { U32.v start <= U32.v finish })
             (inv: nat_at_most finish -> vprop)
             (body:
                    (i:u32_between start finish ->
                          SteelT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : SteelT unit
      (inv (U32.v start))
      (fun _ -> inv (U32.v finish))
