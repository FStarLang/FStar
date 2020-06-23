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

assume val h_admit (#a:Type) (#p:slprop) (#q:a -> slprop) (_:unit) : SteelT a p q

#set-options "--fuel 0 --ifuel 1"

let update_x (r: ref (option u32_pair) u32_pair_pcm) (new_val: UInt32.t)
    : Steel unit (ptr r) (fun _ -> ptr r)
    (fun h0 -> if Some? (sel r h0) then True else False) (fun h0 _ h1 ->
     Some? (sel r h1) /\ Some? (sel r h0) /\
     Some?.v (sel r h1) == { Some?.v (sel r h0) with x = new_val }
    )
  =
  let old_pair = read r in
  let new_pair = (Some ({Some?.v old_pair with x = new_val })) in
  write r new_pair


let get_x (r: ref (option u32_pair) u32_pair_pcm)
  : Steel UInt32.t
  (ptr r) (fun _ -> ptr r)
  (fun h0 -> Some? (sel r h0)) (fun h0 v h1 ->
    Some? (sel r h0) /\ Some? (sel r h1) /\
    sel r h0 == sel r h1 /\ v == (Some?.v (sel r h1)).x
  )
  =
  let pair = read r in
  (Some?.v pair).x


let increment_generic (#cls: rw_pointer UInt32.t) (r: cls.pointer_ref) : Steel unit
  (cls.pointer_slref r) (fun _ -> cls.pointer_slref r)
  (fun h0 -> UInt32.v (cls.pointer_sel r h0) + 1 <= UInt.max_int 32)
  (fun h0 _ h1 ->
    UInt32.v (cls.pointer_sel r h1) == UInt32.v (cls.pointer_sel r h0) + 1
  )
  =
  let old_v = cls.pointer_get r in
  cls.pointer_upd r (UInt32.add old_v 1ul)

let slu32_pair_elim_mem (r: u32_pair_ref) (h: hmem (slu32_pair r)) :
  Lemma (interp (ptr r) h /\ begin let v = sel r h in
    Some? v /\ snd (Some?.v v) == Full
  end)
  =
  elim_h_exists
    (fun (v: u32_pair_stored) -> pts_to r v `star` pure (Some? v /\ snd (Some?.v v) == Full))
    h
    (interp (ptr r) h /\ begin let v = sel r h in
      Some? v /\ snd (Some?.v v) == Full
    end)
    (fun v ->
      intro_h_exists v (pts_to r) h;
      pure_interp (Some? v /\ snd (Some?.v v) == Full) h;
      assert(interp (pure (Some? v /\ snd (Some?.v v) == Full)) h);
      assert(Some? v /\ snd (Some?.v v) == Full);
      let v' = sel_v r v h in
      assert(v' == v)
    )

assume val slu32_pair_elim_steel (r: u32_pair_ref) : Steel unit
  (slu32_pair r)
  (fun _ -> ptr r)
  (fun _ -> True)
  (fun h0 _ h1 ->
    slu32_pair_elim_mem r h0;
    let v = sel r h0 in
    Some? v /\ snd (Some?.v v) == Full /\
    v == sel r h1
  )

assume val slu32_pair_intro_steel (r: u32_pair_ref) : Steel unit
  (ptr r)
  (fun _ -> slu32_pair r)
  (fun h0 -> let v = sel r h0 in
    Some? v /\ snd (Some?.v v) == Full
  )
  (fun h0 _ h1 ->
    slu32_pair_elim_mem r h1;
    sel r h0 == sel r h1
  )

let u32_pair_get : rw_pointer_get_sig u32_pair u32_pair_ref slu32_pair u32_pair_sel =
  fun r ->
    slu32_pair_elim_steel r;
    let pair = read r in
    slu32_pair_intro_steel r;
    fst (Some?.v pair)

let u32_pair_upd: rw_pointer_upd_sig u32_pair u32_pair_ref slu32_pair u32_pair_sel =
  fun r v ->
    slu32_pair_elim_steel r;
    let pair = read r in
    write r (Some (v, snd (Some?.v pair)));
    slu32_pair_intro_steel r

let slu32_pair_x_field_elim_mem (r: u32_pair_x_field_ref) (h: hmem (slu32_pair_x_field r)) :
  Lemma (interp (ptr r) h /\ begin let v = sel r h in
    Some? v /\ (snd (Some?.v v) == XField \/ snd (Some?.v v) == Full)
  end)
  =
  elim_h_exists
    (fun (v: u32_pair_stored) ->
      pts_to r v `star` pure (Some? v /\ (snd (Some?.v v) == XField \/ snd (Some?.v v) == Full))
    )
    h
    (interp (ptr r) h /\ begin let v = sel r h in
      Some? v /\ (snd (Some?.v v) == XField \/ snd (Some?.v v) == Full)
    end)
    (fun v ->
      intro_h_exists v (pts_to r) h;
      pure_interp (Some? v /\ (snd (Some?.v v) == XField \/ snd (Some?.v v) == Full)) h;
      let v' = sel_v r v h in
      ()
    )

assume val slu32_pair_x_field_elim_steel (r: u32_pair_ref) : Steel unit
  (slu32_pair_x_field r)
  (fun _ -> ptr r)
  (fun _ -> True)
  (fun h0 _ h1 ->
    slu32_pair_x_field_elim_mem r h0;
    let v = sel r h0 in
    Some? v /\ (snd (Some?.v v) == XField \/ snd (Some?.v v) == Full) /\
    v == sel r h1
  )

assume val slu32_pair_x_field_intro_steel (r: u32_pair_ref) : Steel unit
  (ptr r)
  (fun _ -> slu32_pair_x_field r)
  (fun h0 -> let v = sel r h0 in
    Some? v /\ (snd (Some?.v v) == XField \/ snd (Some?.v v) == Full)
  )
  (fun h0 _ h1 ->
    slu32_pair_x_field_elim_mem r h1;
    sel r h0 == sel r h1
  )

let u32_pair_x_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field u32_pair_x_field_sel
  =
  fun r ->
    slu32_pair_x_field_elim_steel r;
    let pair = read r in
    slu32_pair_x_field_intro_steel r;
    (fst (Some?.v pair)).x

let u32_pair_x_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field u32_pair_x_field_sel
  =
  fun r v ->
    slu32_pair_x_field_elim_steel r;
    let pair = read r in
    let new_pair = (Some (({ fst (Some?.v pair) with x = v }), snd (Some?.v pair))) in
    frame_preserving_intro u32_pair_stored_pcm pair new_pair
      (fun frame -> ())
      (fun frame ->
        let p = snd (Some?.v pair) in
        match p with
        | XField -> begin match frame with
          | None -> ()
          | Some frame' -> begin match snd frame' with
            | YField ->
              let new_full = op u32_pair_stored_pcm frame new_pair in
              let old_full = op u32_pair_stored_pcm frame pair in
              assume(new_full == new_pair) // We don't have that because the path is Full in new_paip
            | _ -> ()
          end
        end
        | _ -> ()
      );
    assert(FStar.PCM.frame_preserving u32_pair_stored_pcm pair new_pair);
    admit(); // Here the problem is that the write spec uses sel r h0 instead of pair, so we have
             // to prove that because sel r h0 `compatible` pair, the frame preservation still holds
    write r new_pair;
    slu32_pair_x_field_intro_steel r
