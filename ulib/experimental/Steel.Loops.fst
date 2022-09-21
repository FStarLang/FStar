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
open Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Reference
module AT = Steel.Effect.Atomic
module U32 = FStar.UInt32

val for_loop_full' (start:U32.t)
             (finish:U32.t { U32.v start <= U32.v finish })
             (current:U32.t { U32.v start <= U32.v current /\
                               U32.v current <= U32.v finish })

             (inv: nat_at_most finish -> vprop)
             (inv_sel: (i:nat_at_most finish) -> t_of (inv i) -> prop)
             (body:
                    (i:u32_between start finish ->
                          Steel unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))
                          (requires fun h -> inv_sel (U32.v i) (h (inv (U32.v i))))
                          (ensures fun h0 _ h1 ->
                            inv_sel (U32.v i) (h0 (inv (U32.v i))) /\
                            inv_sel (U32.v i + 1) (h1 (inv (U32.v i + 1)))
                          )))
  : Steel unit
      (inv (U32.v current))
      (fun _ -> inv (U32.v finish))
      (requires fun h -> inv_sel (U32.v current) (h (inv (U32.v current))))
      (ensures fun h0 _ h1 ->
        inv_sel (U32.v current) (h0 (inv (U32.v current))) /\
        inv_sel (U32.v finish) (h1 (inv (U32.v finish)))
      )

let rec for_loop_full' start finish current inv inv_sel body
    = if current = finish then (
       AT.change_equal_slprop (inv _) (inv _);
       AT.return ()
    )
    else (
      let _: squash (U32.v current < U32.v finish) = () in //fails without this
      body current;
      let current' = U32.(current +^ 1ul) in
      AT.change_equal_slprop (inv (U32.v current + 1))
                             (inv (U32.v current'));
      for_loop_full' start finish current' inv inv_sel body
    )

(* produces 11 queries *)
let for_loop start finish inv body = for_loop_full' start finish start inv (fun _ _ -> True) body
let for_loop_full start finish inv inv_sel body = for_loop_full' start finish start inv inv_sel body

let rec while_loop inv cond body =
  let b = cond () in
  if b
  then (
     AT.change_equal_slprop (inv b) (inv true);
     body();
     while_loop inv cond body
  )
  else (
     AT.change_equal_slprop (inv b) (inv false);
     AT.return ()
  )
