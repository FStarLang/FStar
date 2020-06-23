(*
   Copyright 2020 Microsoft Research

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

module Steel.ArrayStruct

module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
open Steel.PCM
module PCMBase = Steel.PCM.Base

open Steel.Effect.Fake
open Steel.Memory

let extract_update: unit -> Tot unit = (fun () -> ())
let extract_get: unit -> Tot unit = (fun () -> ())
let extract_explode: unit -> Tot unit = (fun () -> ())
let extract_recombine: unit -> Tot unit = (fun () -> ())
let op_String_Access : unit -> Tot unit = (fun () -> ())
let generic_index: unit -> Tot unit = (fun () -> ())

assume val witness_h_exists (#a:Type) (#p:a -> slprop) (_:unit)
  : SteelT (Ghost.erased a) (h_exists p) (fun x -> p x)

assume val h_assert (p:slprop)
  : SteelT unit p (fun _ -> p)

assume val intro_h_exists (#a:Type) (x:a) (p:(a -> slprop))
  : SteelT unit (p x) (fun _ -> h_exists p)

assume val intro_h_exists_erased (#a:Type) (x:Ghost.erased a) (p:(a -> slprop))
  : SteelT unit (p x) (fun _ -> h_exists p)

assume val reveal_val (#a:Type u#1) (#pcm:pcm a) (r:ref a pcm)
  : Steel (Ghost.erased a) (ptr r) (fun v -> pts_to r v) (fun _ -> True) (fun h0 v h1 ->
    Steel.Memory.intro_h_exists (Ghost.reveal v) (pts_to r) h1;
    sel r h0 == sel r h1 /\ sel r h1 == Ghost.reveal v
  )

#set-options "--fuel 1 --ifuel 0 --print_implicits"

let update_x (r: ref (option u32_pair) u32_pair_pcm) (new_val: UInt32.t)
    : Steel unit (href r) (fun _ -> href r)
    (fun h0 -> if Some? (sel r h0) then True else False) (fun h0 _ h1 ->
     Some? (sel r h1) /\ Some? (sel r h0) /\
     Some?.v (sel r h1) == { Some?.v (sel r h0) with x = new_val }
    )
  =
  let old_pair_ghost : Ghost.erased (option u32_pair) =
    reveal_val r
  in
  let old_pair = read r old_pair_ghost in
  assert(FStar.PCM.compatible u32_pair_pcm (Ghost.reveal old_pair_ghost) old_pair);
  compatible_elim u32_pair_pcm (Ghost.reveal old_pair_ghost) (old_pair)
    (Ghost.reveal old_pair_ghost == old_pair) (fun frame ->
      assert(Some? old_pair_ghost);
      assert(None? frame);
      assert(Some? old_pair);
      assert(Some?.v old_pair_ghost == Some?.v old_pair);
      admit()
    );
  let new_pair = (Some ({Some?.v old_pair with x = new_val })) in
  //write r old_pair new_pair;
  //intro_h_exists new_pair (pts_to r);
  intro_h_exists_erased old_pair_ghost (pts_to r);
  admit()
