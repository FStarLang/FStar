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
module AT = Steel.Effect.Atomic
module US = FStar.SizeT

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
                          SteelT unit
                          (inv (US.v i))
                          (fun _ -> inv (US.v i + 1))))
  : SteelT unit
      (inv (US.v start))
      (fun _ -> inv (US.v finish))

inline_for_extraction
noextract
let for_loop_full
  (start:US.t)
  (finish:US.t { US.v start <= US.v finish })
  (inv: nat_at_most finish -> vprop)
  (inv_sel: (i:nat_at_most finish) -> t_of (inv i) -> prop)
  (body:
    (i:u32_between start finish ->
    Steel unit
    (inv (US.v i))
    (fun _ -> inv (US.v i + 1))
    (requires fun h -> inv_sel (US.v i) (h (inv (US.v i))))
    (ensures fun h0 _ h1 ->
      inv_sel (US.v i) (h0 (inv (US.v i))) /\
      inv_sel (US.v i + 1) (h1 (inv (US.v i + 1)))
    )))
: Steel unit
    (inv (US.v start))
    (fun _ -> inv (US.v finish))
    (requires fun h -> inv_sel (US.v start) (h (inv (US.v start))))
    (ensures fun h0 _ h1 ->
      inv_sel (US.v start) (h0 (inv (US.v start))) /\
      inv_sel (US.v finish) (h1 (inv (US.v finish)))
    )
= AT.intro_vrefine (inv (US.v start)) (inv_sel (US.v start));
  for_loop start finish
    (fun n -> inv n `vrefine` inv_sel n)
    (fun i ->
      AT.elim_vrefine (inv (US.v i)) (inv_sel (US.v i));
      body i;
      AT.intro_vrefine (inv (US.v i + 1)) (inv_sel (US.v i + 1))
    );
  AT.elim_vrefine (inv (US.v finish)) (inv_sel (US.v finish))


/// while_loop: while (cond()) { body () }
val while_loop (inv: Ghost.erased bool -> vprop)
               (cond: (unit -> SteelT bool
                                     (AT.h_exists inv)
                                     (fun b -> inv b)))
               (body: (unit -> SteelT unit
                                     (inv true)
                                     (fun _ -> AT.h_exists inv)))
  : SteelT unit
    (AT.h_exists inv)
     (fun _ -> inv false)
